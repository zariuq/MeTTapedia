Section MetaCat.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition idT : prop := forall X, Obj X -> Hom X X (id X).
Definition compT : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall Z:set, Obj Z ->
 forall f, Hom X Y f ->
 forall g, Hom Y Z g ->
 Hom X Z (comp X Y Z g f).

Definition idL : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall f, Hom X Y f ->
 comp X X Y f (id X) = f.

Definition idR : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall f, Hom X Y f ->
 comp X Y Y (id Y) f = f.

Definition compAssoc : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall Z:set, Obj Z ->
 forall W:set, Obj W ->
 forall f, Hom X Y f ->
 forall g, Hom Y Z g ->
 forall h, Hom Z W h ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition MetaCat : prop := (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.

Lemma MetaCatI : idT -> compT -> idL -> idR -> compAssoc -> MetaCat.
assume H1 H2 H3 H4 H5.
prove (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.
apply and3I.
- apply andI.
  + exact H1.
  + exact H2.
- apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

Lemma MetaCatE : MetaCat -> forall p:prop, (idT -> compT -> idL -> idR -> compAssoc -> p) -> p.
assume H. let p. assume Hp.
apply and3E (idT /\ compT) (idL /\ idR) compAssoc H.
assume H12 H34 H5.
apply H12. assume H1 H2.
apply H34. assume H3 H4.
exact Hp H1 H2 H3 H4 H5.
Qed.

End MetaCat.

Section LocallySmallCat.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition idT' : prop := forall X:set, Obj X -> id X :e Hom X X.
Definition compT' : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall Z:set, Obj Z ->
 forall f :e Hom X Y, forall g :e Hom Y Z,
 comp X Y Z g f :e Hom X Z.

Definition idL' : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall f :e Hom X Y,
 comp X X Y f (id X) = f.

Definition idR' : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall f :e Hom X Y,
 comp X Y Y (id Y) f = f.

Definition compAssoc' : prop :=
 forall X:set, Obj X ->
 forall Y:set, Obj Y ->
 forall Z:set, Obj Z ->
 forall W:set, Obj W ->
 forall f :e Hom X Y, forall g :e Hom Y Z, forall h :e Hom Z W,
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition LocallySmallCat : prop := (idT' /\ compT') /\ (idL' /\ idR') /\ compAssoc'.

Lemma LocallySmallCatI : idT' -> compT' -> idL' -> idR' -> compAssoc' -> LocallySmallCat.
assume H1 H2 H3 H4 H5.
prove (idT' /\ compT') /\ (idL' /\ idR') /\ compAssoc'.
apply and3I.
- apply andI.
  + exact H1.
  + exact H2.
- apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

Lemma LocallySmallCatE : LocallySmallCat -> forall p:prop, (idT' -> compT' -> idL' -> idR' -> compAssoc' -> p) -> p.
assume H. let p. assume Hp.
apply and3E (idT' /\ compT') (idL' /\ idR') compAssoc' H.
assume H12 H34 H5.
apply H12. assume H1 H2.
apply H34. assume H3 H4.
exact Hp H1 H2 H3 H4 H5.
Qed.

Theorem LocallySmallCat_MetaCat : LocallySmallCat -> MetaCat Obj (fun X Y f => f :e Hom X Y) id comp.
assume H. apply LocallySmallCatE H.
assume H1 H2 H3 H4 H5.
apply MetaCatI.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

Section terminal.

Variable X:set.
Variable uniq:set -> set.

Definition LocallySmallCat_terminal : prop :=
    Obj X
 /\ forall Y, Obj Y -> uniq Y :e Hom Y X /\ forall f :e Hom Y X, f = uniq Y.

End terminal.

Section product.

Variable X Y Z piX piY:set.
Variable Pair:set -> set -> set -> set.

Definition LocallySmallCat_product : prop :=
    Obj Z
 /\ piX :e Hom Z X
 /\ piY :e Hom Z Y
 /\ forall W, Obj W -> forall p :e Hom W X, forall q :e Hom W Y,
         Pair W p q :e Hom W Z
      /\ comp W Z X piX (Pair W p q) = p
      /\ comp W Z Y piY (Pair W p q) = q
      /\ forall k :e Hom W Z, comp W Z X piX k = p -> comp W Z Y piY k = q -> Pair W p q = k.

End product.

Section product_constr.

Variable Prod pi0 pi1:set -> set -> set.
Variable Pair:set -> set -> set -> set -> set -> set.

Definition LocallySmallCat_product_constr : prop :=
 forall X Y, Obj X -> Obj Y ->
    LocallySmallCat_product X Y (Prod X Y) (pi0 X Y) (pi1 X Y) (Pair X Y).

Variable Exp Ap:set -> set -> set.
Variable Lam:set -> set -> set -> set -> set.

Definition LocallySmallCat_product_exp_constr : prop :=
 forall X Y, Obj X -> Obj Y ->
      Obj (Exp X Y)
   /\ Ap X Y :e Hom (Prod (Exp X Y) X) Y
   /\ forall Z, Obj Z -> forall f :e Hom (Prod Z X) Y,
           Lam X Y Z f :e Hom Z (Exp X Y)
	/\ (comp (Prod Z X) (Prod (Exp X Y) X) Y
	         (Ap X Y)
	         (Pair (Exp X Y) X (Prod Z X)
		       (comp (Prod Z X) Z (Exp X Y) (Lam X Y Z f) (pi0 Z X))
		       (pi1 Z X)))
             = f
	/\ forall g :e Hom Z (Exp X Y),
              (comp (Prod Z X) (Prod (Exp X Y) X) Y
	            (Ap X Y)
	            (Pair (Exp X Y) X (Prod Z X)
		          (comp (Prod Z X) Z (Exp X Y) g (pi0 Z X))
		          (pi1 Z X)))
                = f
	     -> Lam X Y Z f = g.

End product_constr.

Section pullback.

Variable X Y Z f g W pi0 pi1:set.

Definition LocallySmallCat_pullback : prop :=
    Obj Z
 /\ pi0 :e Hom W X
 /\ pi1 :e Hom W Y
 /\ comp W X Z f pi0 = comp W Y Z g pi1
 /\ forall W', Obj W' -> forall p :e Hom W' X, forall q :e Hom W' Y,
      comp W' X Z f p = comp W' Y Z g q ->
      exists h :e Hom W' W, comp W' W X pi0 h = p /\ comp W' W Y pi1 h = q /\
      forall k :e Hom W' W, comp W' W X pi0 k = p -> comp W' W Y pi1 k = q -> h = k.

End pullback.

Section pullback_constr.

Variable pb : set -> set -> set -> set -> set -> set.
Variable pi0 : set -> set -> set -> set -> set -> set.
Variable pi1 : set -> set -> set -> set -> set -> set.

Definition LocallySmallCat_pullback_constr : prop :=
 forall X Y Z, Obj X -> Obj Y -> Obj Z ->
 forall f :e Hom X Z, forall g :e Hom Y Z,
 LocallySmallCat_pullback X Y Z f g (pb X Y Z f g) (pi0 X Y Z f g) (pi1 X Y Z f g).

End pullback_constr.

Section monic.

Variable X Y f:set.

Definition LocallySmallCat_monic : prop :=
    f :e Hom X Y
 /\ forall Z, Obj Z -> forall g h :e Hom Z X, comp Z X Y f g = comp Z X Y f h -> g = h.

End monic.

End LocallySmallCat.

Section SetLocallySmallCat.

Theorem Set_LocallySmallCat : LocallySmallCat (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)).
apply LocallySmallCatI.
- let X. assume _. prove (fun x :e X => x) :e X :^: X.
  exact lam_Pi X (fun _ => X) (fun x => x) (fun x Hx => Hx).
- let X. assume _. let Y. assume _. let Z. assume _. let f. assume Hf. let g. assume Hg.
  prove (fun x :e X => g (f x)) :e Z :^: X.
  prove (fun x :e X => g (f x)) :e Pi_ x :e X, Z.
  apply lam_Pi X (fun _ => Z) (fun x => g (f x)).
  let x. assume Hx.
  prove g (f x) :e Z.
  apply ap_Pi Y (fun _ => Z) g (f x) Hg.
  prove f x :e Y.
  exact ap_Pi X (fun _ => Y) f x Hf Hx.
- let X. assume _. let Y. assume _. let f. assume Hf.
  prove (fun x :e X => f ((fun x :e X => x) x)) = f.
  transitivity (fun x :e X => f x).
  + apply lam_ext.
    let x. assume Hx.
    prove f ((fun x :e X => x) x) = f x.
    f_equal.
    prove (fun x :e X => x) x = x.
    exact beta X (fun x => x) x Hx.
  + exact Pi_eta X (fun _ => Y) f Hf.
- let X. assume _. let Y. assume _. let f. assume Hf.
  prove (fun x :e X => (fun y :e Y => y) (f x)) = f.
  transitivity (fun x :e X => f x).
  + apply lam_ext.
    let x. assume Hx.
    prove (fun y :e Y => y) (f x) = f x.
    apply beta Y (fun y => y) (f x).
    prove f x :e Y.
    exact ap_Pi X (fun _ => Y) f x Hf Hx.
  + exact Pi_eta X (fun _ => Y) f Hf.
- let X. assume _. let Y. assume _. let Z. assume _. let W. assume _.
  let f. assume Hf. let g. assume Hg. let h. assume Hh.
  prove (fun x :e X => ((fun y :e Y => h (g y)) (f x)))
      = (fun x :e X => h ((fun x :e X => g (f x)) x)).
  apply lam_ext.
  let x. assume Hx.
  transitivity h (g (f x)).
  + prove (fun y :e Y => h (g y)) (f x) = h (g (f x)).
    apply beta Y (fun y => h (g y)) (f x).
    prove f x :e Y.
    exact ap_Pi X (fun _ => Y) f x Hf Hx.
  + prove h (g (f x)) = h ((fun x :e X => g (f x)) x).
    f_equal. symmetry.
    exact beta X (fun x => g (f x)) x Hx.
Qed.

End SetLocallySmallCat.

Section SmallCat.

Variable Obj: set.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition idT'' : prop := forall X:set, X :e Obj -> id X :e Hom X X.
Definition compT'' : prop :=
 forall X Y Z :e Obj,
 forall f :e Hom X Y,
 forall g :e Hom Y Z,
 comp X Y Z g f :e Hom X Z.

Definition idL'' : prop :=
 forall X Y :e Obj, forall f :e Hom X Y,
 comp X X Y f (id X) = f.

Definition idR'' : prop :=
 forall X Y :e Obj, forall f :e Hom X Y,
 comp X Y Y (id Y) f = f.

Definition compAssoc'' : prop :=
 forall X Y Z W :e Obj,
 forall f :e Hom X Y,
 forall g :e Hom Y Z,
 forall h :e Hom Z W,
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition SmallCat : prop := (idT'' /\ compT'') /\ (idL'' /\ idR'') /\ compAssoc''.

Lemma SmallCatI : idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> SmallCat.
assume H1 H2 H3 H4 H5.
prove (idT'' /\ compT'') /\ (idL'' /\ idR'') /\ compAssoc''.
apply and3I.
- apply andI.
  + exact H1.
  + exact H2.
- apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

Lemma SmallCatE : SmallCat -> forall p:prop, (idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> p) -> p.
assume H. let p. assume Hp.
apply and3E (idT'' /\ compT'') (idL'' /\ idR'') compAssoc'' H.
assume H12 H34 H5.
apply H12. assume H1 H2.
apply H34. assume H3 H4.
exact Hp H1 H2 H3 H4 H5.
Qed.

Theorem SmallCat_LocallySmallCat : SmallCat -> LocallySmallCat (fun X => X :e Obj) Hom id comp.
assume H. apply SmallCatE H.
assume H1 H2 H3 H4 H5.
apply LocallySmallCatI.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

Theorem SmallCat_MetaCat : SmallCat -> MetaCat (fun X => X :e Obj) (fun X Y f => f :e Hom X Y) id comp.
assume H.
apply LocallySmallCat_MetaCat.
apply SmallCat_LocallySmallCat.
exact H.
Qed.

Definition SmallCatAsObject : set := 
(Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)).

End SmallCat.

Definition SmallCatAsObjectP : set -> prop :=
fun C =>
tuple_p 4 C /\ SmallCat (C 0) (fun X Y => C 1 X Y) (fun X => C 2 X) (fun X Y Z g f => C 3 X Y Z g f).

Theorem SmallCatAsObject_1 :
forall (Obj:set) (Hom:set -> set -> set) (id:set->set) (comp:set->set->set->set->set->set),
SmallCat Obj Hom id comp ->
SmallCatAsObject Obj Hom id comp 0 = Obj
/\
(forall X Y :e Obj, SmallCatAsObject Obj Hom id comp 1 X Y = Hom X Y)
/\
(forall X :e Obj,SmallCatAsObject Obj Hom id comp 2 X = id X)
/\
(forall (X Y Z :e Obj) (g :e Hom Y Z) (f :e Hom X Y), SmallCatAsObject Obj Hom id comp 3 X Y Z g f = comp X Y Z g f)
/\
SmallCatAsObjectP (SmallCatAsObject Obj Hom id comp).
let Obj Hom id comp.
assume H.
set C := SmallCatAsObject Obj Hom id comp.
claim L0: C 0 = Obj.
{ prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 0 = Obj.
  apply tuple_4_0_eq.
}
claim L1: forall X Y :e Obj, C 1 X Y = Hom X Y.
{ let X. assume HX. let Y. assume HY.
  prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 1 X Y = Hom X Y.
  rewrite tuple_4_1_eq.
  prove (fun X :e Obj => fun Y :e Obj => Hom X Y) X Y = Hom X Y.
  rewrite beta Obj (fun X => fun Y :e Obj => Hom X Y) X HX.
  exact beta Obj (fun Y => Hom X Y) Y HY.
}
claim L2: forall X :e Obj, C 2 X = id X.
{ let X. assume HX.
  prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 2 X = id X.
  rewrite tuple_4_2_eq.
  prove (fun X :e Obj => id X) X = id X.
  exact beta Obj (fun X => id X) X HX.
}
claim L3: forall X Y Z :e Obj, forall g :e Hom Y Z, forall f :e Hom X Y, C 3 X Y Z g f = comp X Y Z g f.
{ let X. assume HX. let Y. assume HY. let Z. assume HZ. let g. assume Hg. let f. assume Hf.
  prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 3 X Y Z g f = comp X Y Z g f.
  rewrite tuple_4_3_eq.
  prove (fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f) X Y Z g f = comp X Y Z g f.
  rewrite beta Obj (fun X => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f) X HX.
  rewrite beta Obj (fun Y => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f) Y HY.
  rewrite beta Obj (fun Z => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f) Z HZ.
  rewrite beta (Hom Y Z) (fun g => fun f :e Hom X Y => comp X Y Z g f) g Hg.
  exact beta (Hom X Y) (fun f => comp X Y Z g f) f Hf.
}
apply and5I.
- exact L0.
- exact L1.
- exact L2.
- exact L3.
- prove tuple_p 4 C
     /\ SmallCat (C 0) (fun X Y => C 1 X Y) (fun X => C 2 X) (fun X Y Z g f => C 3 X Y Z g f).
  apply andI.
  + prove tuple_p 4 (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)).
    apply tuple_p_4_tuple.
  + apply SmallCatE Obj Hom id comp H.
    assume H1 H2 H3 H4 H5.
    apply SmallCatI.
    * prove forall X :e C 0, C 2 X :e C 1 X X.
      rewrite L0.
      let X.
      assume HX: X :e Obj.
      rewrite L2 X HX.
      rewrite L1 X HX X HX.
      exact H1 X HX.
    * prove forall X Y Z :e C 0, forall f :e C 1 X Y, forall g :e C 1 Y Z, C 3 X Y Z g f :e C 1 X Z.
      rewrite L0.
      let X. assume HX. let Y. assume HY. let Z. assume HZ.
      rewrite L1 X HX Y HY.
      let f. assume Hf.
      rewrite L1 Y HY Z HZ.
      let g. assume Hg.
      rewrite L1 X HX Z HZ.
      rewrite L3 X HX Y HY Z HZ g Hg f Hf.
      exact H2 X HX Y HY Z HZ f Hf g Hg.
    * rewrite L0.
      let X. assume HX: X :e Obj. let Y. assume HY: Y :e Obj.
      rewrite L1 X HX Y HY.
      let f. assume Hf: f :e Hom X Y.
      rewrite L2 X HX.
      prove C 3 X X Y f (id X) = f.
      rewrite L3 X HX X HX Y HY f Hf (id X) (H1 X HX).
      exact H3 X HX Y HY f Hf.
    * rewrite L0.
      let X. assume HX: X :e Obj. let Y. assume HY: Y :e Obj.
      rewrite L1 X HX Y HY.
      let f. assume Hf: f :e Hom X Y.
      rewrite L2 Y HY.
      prove C 3 X Y Y (id Y) f = f.
      rewrite L3 X HX Y HY Y HY (id Y) (H1 Y HY) f Hf.
      exact H4 X HX Y HY f Hf.
    * rewrite L0.
      let X. assume HX: X :e Obj. let Y. assume HY: Y :e Obj.
      let Z. assume HZ: Z :e Obj. let W. assume HW: W :e Obj.
      rewrite L1 X HX Y HY.
      let f. assume Hf: f :e Hom X Y.
      rewrite L1 Y HY Z HZ.
      let g. assume Hg: g :e Hom Y Z.
      rewrite L1 Z HZ W HW.
      let h. assume Hh: h :e Hom Z W.
      rewrite L3 X HX Y HY Z HZ g Hg f Hf.
      rewrite L3 Y HY Z HZ W HW h Hh g Hg.
      rewrite L3 X HX Y HY W HW (comp Y Z W h g) (H2 Y HY Z HZ W HW g Hg h Hh) f Hf.
      rewrite L3 X HX Z HZ W HW h Hh (comp X Y Z g f) (H2 X HX Y HY Z HZ f Hf g Hg).
      exact H5 X HX Y HY Z HZ W HW f Hf g Hg h Hh.
Qed.

Section OpCat.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Theorem LocallySmallCat_OpCat:
    LocallySmallCat Obj Hom id comp
 -> LocallySmallCat Obj (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g).
assume H. apply LocallySmallCatE Obj Hom id comp H.
assume H1 H2 H3 H4 H5.
apply LocallySmallCatI.
- exact H1.
- let X. assume HX. let Y. assume HY. let Z. assume HZ.
  let f. assume Hf. let g. assume Hg.
  exact H2 Z HZ Y HY X HX g Hg f Hf.
- let X. assume HX. let Y. assume HY.
  exact H4 Y HY X HX.
- let X. assume HX. let Y. assume HY.
  exact H3 Y HY X HX.
- let X. assume HX. let Y. assume HY.
  let Z. assume HZ. let W. assume HW.
  let f. assume Hf. let g. assume Hg. let h. assume Hh.
  symmetry.
  exact H5 W HW Z HZ Y HY X HX h Hh g Hg f Hf.
Qed.

End OpCat.

Section OpCat.

Variable Obj: set.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Theorem SmallCat_OpCat:
    SmallCat Obj Hom id comp
 -> SmallCat Obj (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g).
assume H. apply SmallCatE Obj Hom id comp H.
assume H1 H2 H3 H4 H5.
apply SmallCatI.
- exact H1.
- let X. assume HX. let Y. assume HY. let Z. assume HZ.
  let f. assume Hf. let g. assume Hg.
  exact H2 Z HZ Y HY X HX g Hg f Hf.
- let X. assume HX. let Y. assume HY.
  exact H4 Y HY X HX.
- let X. assume HX. let Y. assume HY.
  exact H3 Y HY X HX.
- let X. assume HX. let Y. assume HY.
  let Z. assume HZ. let W. assume HW.
  let f. assume Hf. let g. assume Hg. let h. assume Hh.
  symmetry.
  exact H5 W HW Z HZ Y HY X HX h Hh g Hg f Hf.
Qed.

End OpCat.

Section SliceCat.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable c : set.

Theorem LocallySmallCat_SliceCat:
    LocallySmallCat Obj Hom id comp
 -> Obj c
 -> LocallySmallCat (fun X => Obj (X 0) /\ X 1 :e Hom (X 0) c)
                    (fun X Y => {g :e Hom (X 0) (Y 0) | comp (X 0) (Y 0) c (Y 1) g = X 1})
		    (fun X => id (X 0))
		    (fun X Y Z g f => comp (X 0) (Y 0) (Z 0) g f).
assume H Hc. apply LocallySmallCatE Obj Hom id comp H.
assume H1 H2 H3 H4 H5.
apply LocallySmallCatI.
- let X. assume HX. apply HX.
  assume HX0: Obj (X 0).
  assume HX1: X 1 :e Hom (X 0) c.
  prove id (X 0) :e {g :e Hom (X 0) (X 0) | comp (X 0) (X 0) c (X 1) g = X 1}.
  apply SepI.
  + apply H1. exact HX0.
  + prove comp (X 0) (X 0) c (X 1) (id (X 0)) = X 1.
    apply H3.
    * exact HX0.
    * exact Hc.
    * exact HX1.
- let X. assume HX.
  let Y. assume HY.
  let Z. assume HZ.
  let f. assume Hf: f :e {g :e Hom (X 0) (Y 0) | comp (X 0) (Y 0) c (Y 1) g = X 1}.
  let g. assume Hg: g :e {g :e Hom (Y 0) (Z 0) | comp (Y 0) (Z 0) c (Z 1) g = Y 1}.
  apply HX.
  assume HX0: Obj (X 0).
  assume HX1: X 1 :e Hom (X 0) c.
  apply HY.
  assume HY0: Obj (Y 0).
  assume HY1: Y 1 :e Hom (Y 0) c.
  apply HZ.
  assume HZ0: Obj (Z 0).
  assume HZ1: Z 1 :e Hom (Z 0) c.
  apply SepE (Hom (X 0) (Y 0)) (fun g => comp (X 0) (Y 0) c (Y 1) g = X 1) f Hf.
  assume Hf0 Hf1.
  apply SepE (Hom (Y 0) (Z 0)) (fun g => comp (Y 0) (Z 0) c (Z 1) g = Y 1) g Hg.
  assume Hg0 Hg1.
  prove comp (X 0) (Y 0) (Z 0) g f :e {g :e Hom (X 0) (Z 0) | comp (X 0) (Z 0) c (Z 1) g = X 1}.
  apply SepI.
  + prove comp (X 0) (Y 0) (Z 0) g f :e Hom (X 0) (Z 0).
    apply H2.
    * exact HX0.
    * exact HY0.
    * exact HZ0.
    * exact Hf0.
    * exact Hg0.
  + prove comp (X 0) (Z 0) c (Z 1) (comp (X 0) (Y 0) (Z 0) g f) = X 1.
    rewrite <- H5 (X 0) HX0 (Y 0) HY0 (Z 0) HZ0 c Hc f Hf0 g Hg0 (Z 1) HZ1.
    prove comp (X 0) (Y 0) c (comp (Y 0) (Z 0) c (Z 1) g) f = X 1.
    rewrite Hg1.
    prove comp (X 0) (Y 0) c (Y 1) f = X 1.
    exact Hf1.
- let X. assume HX.
  let Y. assume HY.
  let f. assume Hf: f :e {g :e Hom (X 0) (Y 0) | comp (X 0) (Y 0) c (Y 1) g = X 1}.
  apply HX.
  assume HX0: Obj (X 0).
  assume HX1: X 1 :e Hom (X 0) c.
  apply HY.
  assume HY0: Obj (Y 0).
  assume HY1: Y 1 :e Hom (Y 0) c.
  apply SepE (Hom (X 0) (Y 0)) (fun g => comp (X 0) (Y 0) c (Y 1) g = X 1) f Hf.
  assume Hf0 Hf1.
  prove comp (X 0) (X 0) (Y 0) f (id (X 0)) = f.
  apply H3.
  + exact HX0.
  + exact HY0.
  + exact Hf0.
- let X. assume HX.
  let Y. assume HY.
  let f. assume Hf: f :e {g :e Hom (X 0) (Y 0) | comp (X 0) (Y 0) c (Y 1) g = X 1}.
  apply HX.
  assume HX0: Obj (X 0).
  assume HX1: X 1 :e Hom (X 0) c.
  apply HY.
  assume HY0: Obj (Y 0).
  assume HY1: Y 1 :e Hom (Y 0) c.
  apply SepE (Hom (X 0) (Y 0)) (fun g => comp (X 0) (Y 0) c (Y 1) g = X 1) f Hf.
  assume Hf0 Hf1.
  prove comp (X 0) (Y 0) (Y 0) (id (Y 0)) f = f.
  apply H4.
  + exact HX0.
  + exact HY0.
  + exact Hf0.
- let X. assume HX.
  let Y. assume HY.
  let Z. assume HZ.
  let W. assume HW.
  let f. assume Hf: f :e {g :e Hom (X 0) (Y 0) | comp (X 0) (Y 0) c (Y 1) g = X 1}.
  let g. assume Hg: g :e {g :e Hom (Y 0) (Z 0) | comp (Y 0) (Z 0) c (Z 1) g = Y 1}.
  let h. assume Hh: h :e {g :e Hom (Z 0) (W 0) | comp (Z 0) (W 0) c (W 1) g = Z 1}.
  apply HX.
  assume HX0: Obj (X 0).
  assume HX1: X 1 :e Hom (X 0) c.
  apply HY.
  assume HY0: Obj (Y 0).
  assume HY1: Y 1 :e Hom (Y 0) c.
  apply HZ.
  assume HZ0: Obj (Z 0).
  assume HZ1: Z 1 :e Hom (Z 0) c.
  apply HW.
  assume HW0: Obj (W 0).
  assume HW1: W 1 :e Hom (W 0) c.
  apply SepE (Hom (X 0) (Y 0)) (fun g => comp (X 0) (Y 0) c (Y 1) g = X 1) f Hf.
  assume Hf0 Hf1.
  apply SepE (Hom (Y 0) (Z 0)) (fun g => comp (Y 0) (Z 0) c (Z 1) g = Y 1) g Hg.
  assume Hg0 Hg1.
  apply SepE (Hom (Z 0) (W 0)) (fun g => comp (Z 0) (W 0) c (W 1) g = Z 1) h Hh.
  assume Hh0 Hh1.
  prove comp (X 0) (Y 0) (W 0) (comp (Y 0) (Z 0) (W 0) h g) f
      = comp (X 0) (Z 0) (W 0) h (comp (X 0) (Y 0) (Z 0) g f).
  apply H5.
  + exact HX0.
  + exact HY0.
  + exact HZ0.
  + exact HW0.
  + exact Hf0.
  + exact Hg0.
  + exact Hh0.
Qed.

End SliceCat.

Section Functor.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.
Variable F0: set -> set.
Variable F1: set -> set -> set -> set.

Definition Functor : prop :=
 forall p:prop,
     ((forall X, Obj X -> Obj' (F0 X))
   -> (forall X, Obj X -> forall Y, Obj Y -> forall f :e Hom X Y, F1 X Y f :e Hom' (F0 X) (F0 Y))
   -> (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
   -> (forall X, Obj X -> forall Y, Obj Y -> forall Z, Obj Z ->
       forall g :e Hom Y Z, forall f :e Hom X Y,
       F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f))
   -> p)
  -> p.

Theorem FunctorI : (forall X, Obj X -> Obj' (F0 X))
   -> (forall X, Obj X -> forall Y, Obj Y -> forall f :e Hom X Y, F1 X Y f :e Hom' (F0 X) (F0 Y))
   -> (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
   -> (forall X, Obj X -> forall Y, Obj Y -> forall Z, Obj Z ->
       forall g :e Hom Y Z, forall f :e Hom X Y,
       F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f))
   -> Functor.
assume H1 H2 H3 H4. let p. assume Hp.
exact Hp H1 H2 H3 H4.
Qed.

End Functor.

Section Presheaf.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Variable F0: set -> set.
Variable F1: set -> set -> set -> set.

Definition Presheaf : prop :=
 Functor Obj (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g) (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)) F0 F1.

End Presheaf.

Section NatTrans.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set.
Variable comp': set -> set -> set -> set -> set -> set.
Variable F0: set -> set.
Variable F1: set -> set -> set -> set.
Variable G0: set -> set.
Variable G1: set -> set -> set -> set.
Variable eta: set -> set.

Definition NatTrans : prop :=
     (forall X, Obj X -> eta X :e Hom' (F0 X) (G0 X))
  /\ (forall X, Obj X -> forall Y, Obj Y -> forall h :e Hom X Y,
         comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y h)
       = comp' (F0 X) (G0 X) (G0 Y) (G1 X Y h) (eta X)).

Theorem NatTransI :
    (forall X, Obj X -> eta X :e Hom' (F0 X) (G0 X))
 -> (forall X, Obj X -> forall Y, Obj Y -> forall h :e Hom X Y,
         comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y h)
       = comp' (F0 X) (G0 X) (G0 Y) (G1 X Y h) (eta X))
 -> NatTrans.
exact andI (forall X, Obj X -> eta X :e Hom' (F0 X) (G0 X))
           (forall X, Obj X -> forall Y, Obj Y -> forall h :e Hom X Y,
               comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y h)
             = comp' (F0 X) (G0 X) (G0 Y) (G1 X Y h) (eta X)).
Qed.

End NatTrans.

Section NatTrans.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set.
Variable comp': set -> set -> set -> set -> set -> set.
Variable F0: set -> set.
Variable F1: set -> set -> set -> set.
Variable G0: set -> set.
Variable G1: set -> set -> set -> set.
Variable eta eta': set -> set.

Theorem NatTrans_ext : (forall X, Obj X -> eta X = eta' X)
 -> NatTrans Obj Hom Obj' Hom' comp' F0 F1 G0 G1 eta
 -> NatTrans Obj Hom Obj' Hom' comp' F0 F1 G0 G1 eta'.
assume H1 H2.
apply H2.
assume H3 H4.
prove (forall X, Obj X -> eta' X :e Hom' (F0 X) (G0 X))
   /\ (forall X, Obj X -> forall Y, Obj Y -> forall h :e Hom X Y,
          comp' (F0 X) (F0 Y) (G0 Y) (eta' Y) (F1 X Y h)
        = comp' (F0 X) (G0 X) (G0 Y) (G1 X Y h) (eta' X)).
apply andI.
- let X. assume HX. rewrite <- H1 X HX.
  exact H3 X HX.
- let X. assume HX. let Y. assume HY.
  rewrite <- H1 X HX.
  rewrite <- H1 Y HY.
  exact H4 X HX Y HY.
Qed.

End NatTrans.

Section FunctorCat.

Variable Obj: set.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.

Hypothesis HC: SmallCat Obj Hom id comp.
Hypothesis HC': LocallySmallCat Obj' Hom' id' comp'.

Theorem LocallySmallCat_FunctorCat :
  LocallySmallCat
    (fun F => Functor (fun X => X :e Obj) Hom id comp Obj' Hom' id' comp' (fun X => F 0 X) (fun X Y f => F 1 X Y f))
    (fun F G => {eta :e Pi_ X :e Obj, Hom' (F 0 X) (G 0 X) |
                  NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
                           (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                           (fun X => G 0 X) (fun X Y f => G 1 X Y f)
                           (fun X => eta X)})
    (fun F => fun X :e Obj => id' (F 0 X))
    (fun F G H xi eta => fun X :e Obj => comp' (F 0 X) (G 0 X) (H 0 X) (xi X) (eta X)).
apply SmallCatE Obj Hom id comp HC.
assume HC1 HC2 HC3 HC4 HC5.
apply LocallySmallCatE Obj' Hom' id' comp' HC'.
assume HC'1 HC'2 HC'3 HC'4 HC'5.
set Obj'' : set -> prop := fun F => Functor (fun X => X :e Obj) Hom id comp Obj' Hom' id' comp' (fun X => F 0 X) (fun X Y f => F 1 X Y f).
set Hom'' : set -> set -> set := fun F G =>
  {eta :e Pi_ X :e Obj, Hom' (F 0 X) (G 0 X) |
                  NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
                           (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                           (fun X => G 0 X) (fun X Y f => G 1 X Y f)
                           (fun X => eta X)}.
set id'' : set -> set := fun F => fun X :e Obj => id' (F 0 X).
set comp'' : set -> set -> set -> set -> set -> set :=
  fun F G H xi eta => fun X :e Obj => comp' (F 0 X) (G 0 X) (H 0 X) (xi X) (eta X).

claim LHom''I: forall F G eta, eta :e (Pi_ X :e Obj, Hom' (F 0 X) (G 0 X))
 -> NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
             (fun X => F 0 X) (fun X Y f => F 1 X Y f)
             (fun X => G 0 X) (fun X Y f => G 1 X Y f)
             (fun X => eta X)
 -> eta :e Hom'' F G.
{ let F G eta. assume H1 H2.
  prove eta :e {eta :e Pi_ X :e Obj, Hom' (F 0 X) (G 0 X) |
                  NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
                           (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                           (fun X => G 0 X) (fun X Y f => G 1 X Y f)
                           (fun X => eta X)}.
  apply SepI.
  - exact H1.
  - exact H2.
}
claim LHom''I2: forall F G, forall eta:set -> set,
    (forall X :e Obj, eta X :e Hom' (F 0 X) (G 0 X))
 -> NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
             (fun X => F 0 X) (fun X Y f => F 1 X Y f)
             (fun X => G 0 X) (fun X Y f => G 1 X Y f)
             eta
 -> (fun X :e Obj => eta X) :e Hom'' F G.
{ let F G eta. assume H1 H2.
  apply LHom''I.
  - prove (fun X :e Obj => eta X) :e (Pi_ X :e Obj, Hom' (F 0 X) (G 0 X)).
    apply lam_Pi.
    exact H1.
  - prove NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
             (fun X => F 0 X) (fun X Y f => F 1 X Y f)
             (fun X => G 0 X) (fun X Y f => G 1 X Y f)
             (fun X => (fun X :e Obj => eta X) X).
    apply NatTrans_ext (fun X => X :e Obj) Hom Obj' Hom' comp'
             (fun X => F 0 X) (fun X Y f => F 1 X Y f)
             (fun X => G 0 X) (fun X Y f => G 1 X Y f)
	     eta
             (fun X => (fun X :e Obj => eta X) X).
    + let X. assume HX.
      prove eta X = (fun X :e Obj => eta X) X.
      symmetry. exact beta Obj eta X HX.
    + exact H2.
}
apply LocallySmallCatI.
- let F. assume HF: Obj'' F.
  apply HF.
  assume HF1 HF2 HF3 HF4.
  prove id'' F :e Hom'' F F.
  prove (fun X :e Obj => id' (F 0 X)) :e Hom'' F F.
  set eta : set -> set := fun X:set => id' (F 0 X).
  prove (fun X :e Obj => eta X) :e Hom'' F F.
  apply LHom''I2.
  + let X. assume HX.
    prove eta X :e Hom' (F 0 X) (F 0 X).
    prove id' (F 0 X) :e Hom' (F 0 X) (F 0 X).
    apply HC'1 (F 0 X).
    prove Obj' (F 0 X).
    exact HF1 X HX.
  + prove NatTrans (fun X => X :e Obj) Hom Obj' Hom' comp'
                   (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                   (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                   eta.
    admit.
- let F. assume HF: Obj'' F.
  let G. assume HG: Obj'' G.
  let H. assume HH: Obj'' H.
  let eta. assume Heta: eta :e Hom'' F G.
  let xi. assume Hxi: xi :e Hom'' G H.
  prove comp'' F G H xi eta :e Hom'' F H.
  admit.
- let F. assume HF: Obj'' F.
  let G. assume HG: Obj'' G.
  let eta. assume Heta: eta :e Hom'' F G.
  prove comp'' F F G eta (id'' F) = eta.
  admit.
- let F. assume HF: Obj'' F.
  let G. assume HG: Obj'' G.
  let eta. assume Heta: eta :e Hom'' F G.
  prove comp'' F G G (id'' G) eta = eta.
  admit.
- let F. assume HF: Obj'' F.
  let G. assume HG: Obj'' G.
  let H. assume HH: Obj'' H.
  let J. assume HJ: Obj'' J.
  let eta. assume Heta: eta :e Hom'' F G.
  let xi. assume Hxi: xi :e Hom'' G H.
  let mu. assume Hmu: mu :e Hom'' H J.
  prove comp'' F G J (comp'' G H J mu xi) eta = comp'' F H J mu (comp'' F G H xi eta).
  admit.
Qed.

End FunctorCat.

Section PresheafCat.

Variable Obj: set.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Hypothesis HC: SmallCat Obj Hom id comp.

Theorem LocallySmallCat_PresheafCat :
  LocallySmallCat
    (fun F => Presheaf (fun X => X :e Obj) Hom id comp
                       (fun X => F 0 X) (fun X Y f => F 1 X Y f))
    (fun F G => {eta :e Pi_ X :e Obj, G 0 X :^: F 0 X |
                  NatTrans (fun X => X :e Obj) (fun X Y => Hom Y X) (fun _ => True) (fun X Y => Y :^: X) (fun X Y Z g f => fun x :e X => g (f x))
                           (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                           (fun X => G 0 X) (fun X Y f => G 1 X Y f)
                           (fun X => eta X)})
    (fun F => fun X :e Obj => fun x :e F 0 X => x)
    (fun F G H xi eta => fun X :e Obj => fun x :e F 0 X => xi X (eta X x)).
prove
  LocallySmallCat
    (fun F => Functor (fun X => X :e Obj) (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g)
                      (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x))
                      (fun X => F 0 X) (fun X Y f => F 1 X Y f))
    (fun F G => {eta :e Pi_ X :e Obj, G 0 X :^: F 0 X |
                  NatTrans (fun X => X :e Obj) (fun X Y => Hom Y X) (fun _ => True) (fun X Y => Y :^: X) (fun X Y Z g f => fun x :e X => g (f x))
                           (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                           (fun X => G 0 X) (fun X Y f => G 1 X Y f)
                           (fun X => eta X)})
    (fun F => fun X :e Obj => fun x :e F 0 X => x)
    (fun F G H xi eta => fun X :e Obj => fun x :e F 0 X => xi X (eta X x)).
apply LocallySmallCat_FunctorCat
          Obj (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g)
	  (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)).
- prove SmallCat Obj (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g).
  apply SmallCat_OpCat.
  exact HC.
- prove LocallySmallCat (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)).
  exact Set_LocallySmallCat.
Qed.

End PresheafCat.

Section Yoneda.

Variable Obj: set.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition yoneda0 : set -> set := fun X =>
 ((fun Y :e Obj => Hom Y X),
  (fun Z :e Obj => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f)).

Definition yoneda1 : set -> set -> set -> set := fun X X' f =>
 fun Y :e Obj => fun g :e Hom Y X => comp Y X X' f g.

Hypothesis HC: SmallCat Obj Hom id comp.

Theorem yoneda0_Presheaf: forall X :e Obj,
  Presheaf (fun Y => Y :e Obj) Hom id comp
           (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f).
let X. assume HX.
prove Functor (fun Y => Y :e Obj) (fun X Y => Hom Y X) id (fun X Y Z g f => comp Z Y X f g)
              (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x)
	      (fun X Y Z g f => fun x :e X => g (f x))
	      (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f).
apply SmallCatE Obj Hom id comp HC.
assume HC1 HC2 HC3 HC4 HC5.
set yon00 : set := (fun Y :e Obj => Hom Y X).
set yon01 : set := (fun Z :e Obj => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f).
claim L0: forall Y :e Obj, yoneda0 X 0 Y = Hom Y X.
{ let Y. assume HY.
  prove (yon00,yon01) 0 Y = Hom Y X.
  rewrite tuple_2_0_eq.
  prove yon00 Y = Hom Y X.
  exact beta Obj (fun Y => Hom Y X) Y HY.
}
claim L1: forall Y Z :e Obj, forall f :e Hom Y Z, yoneda0 X 1 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
{ let Y. assume HY. let Z. assume HZ. let f. assume Hf.
  prove (yon00,yon01) 1 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
  rewrite tuple_2_1_eq.
  prove yon01 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
  rewrite beta Obj (fun Z => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f) Z HZ.
  rewrite beta Obj (fun Y => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f) Y HY.
  exact beta (Hom Y Z) (fun f => fun g :e Hom Z X => comp Y Z X g f) f Hf.
}
claim L2: forall Y Z :e Obj, forall f :e Hom Z Y, yoneda0 X 1 Y Z f :e (Hom Z X) :^: (Hom Y X).
{ let Y. assume HY. let Z. assume HZ.
  let f. assume Hf: f :e Hom Z Y.
  rewrite L1 Z HZ Y HY f Hf.
  prove (fun g :e Hom Y X => comp Z Y X g f) :e Hom Z X :^: Hom Y X.
  prove (fun g :e Hom Y X => comp Z Y X g f) :e Pi_ g :e Hom Y X, Hom Z X.
  apply lam_Pi.
  let g. assume Hg: g :e Hom Y X.
  prove comp Z Y X g f :e Hom Z X.
  exact HC2 Z HZ Y HY X HX f Hf g Hg.
}
claim L3: forall Y Z :e Obj, forall f :e Hom Z Y, yoneda0 X 1 Y Z f :e (yoneda0 X 0 Z) :^: (yoneda0 X 0 Y).
{ let Y. assume HY. let Z. assume HZ.
  let f. assume Hf: f :e Hom Z Y.
  prove yoneda0 X 1 Y Z f :e (yoneda0 X 0 Z) :^: (yoneda0 X 0 Y).
  rewrite L0 Y HY.
  rewrite L0 Z HZ.
  prove yoneda0 X 1 Y Z f :e Hom Z X :^: Hom Y X.
  exact L2 Y HY Z HZ f Hf.
}
apply FunctorI.
- let Y. assume _. exact TrueI.
- exact L3.
- let Y. assume HY.
  prove yoneda0 X 1 Y Y (id Y) = fun g :e yoneda0 X 0 Y => g.
  rewrite L0 Y HY.
  prove yoneda0 X 1 Y Y (id Y) = fun g :e Hom Y X => g.
  rewrite L1 Y HY Y HY (id Y) (HC1 Y HY).
  prove (fun g :e Hom Y X => comp Y Y X g (id Y)) = (fun g :e Hom Y X => g).
  apply lam_ext.
  let g. assume Hg: g :e Hom Y X.
  exact HC3 Y HY X HX g Hg.
- let Y. assume HY. let Z. assume HZ. let W. assume HW.
  let g. assume Hg: g :e Hom W Z.
  let f. assume Hf: f :e Hom Z Y.
  prove yoneda0 X 1 Y W (comp W Z Y f g) = (fun h :e yoneda0 X 0 Y => yoneda0 X 1 Z W g (yoneda0 X 1 Y Z f h)).
  rewrite L0 Y HY.
  prove yoneda0 X 1 Y W (comp W Z Y f g) = (fun h :e Hom Y X => yoneda0 X 1 Z W g (yoneda0 X 1 Y Z f h)).
  rewrite L1 W HW Y HY (comp W Z Y f g) (HC2 W HW Z HZ Y HY g Hg f Hf).
  prove (fun h :e Hom Y X => comp W Y X h (comp W Z Y f g))
      = (fun h :e Hom Y X => yoneda0 X 1 Z W g (yoneda0 X 1 Y Z f h)).
  apply lam_ext.
  let h. assume Hh: h :e Hom Y X.
  prove comp W Y X h (comp W Z Y f g) = yoneda0 X 1 Z W g (yoneda0 X 1 Y Z f h).
  rewrite L1 W HW Z HZ g Hg.
  prove comp W Y X h (comp W Z Y f g) = (fun k :e Hom Z X => comp W Z X k g) (yoneda0 X 1 Y Z f h).
  rewrite L1 Z HZ Y HY f Hf.
  prove comp W Y X h (comp W Z Y f g) = (fun k :e Hom Z X => comp W Z X k g) ((fun k :e Hom Y X => comp Z Y X k f) h).
  rewrite beta (Hom Y X) (fun k => comp Z Y X k f) h Hh.
  prove comp W Y X h (comp W Z Y f g) = (fun k :e Hom Z X => comp W Z X k g) (comp Z Y X h f).
  rewrite beta (Hom Z X) (fun k => comp W Z X k g) (comp Z Y X h f)
               (HC2 Z HZ Y HY X HX f Hf h Hh).
  prove comp W Y X h (comp W Z Y f g) = comp W Z X (comp Z Y X h f) g. 
  symmetry.
  exact HC5 W HW Z HZ Y HY X HX g Hg f Hf h Hh.
Qed.

Theorem yoneda1_NatTrans: forall X X' :e Obj, forall f :e Hom X X',
  NatTrans (fun Y => Y :e Obj) (fun X Y => Hom Y X)
           (fun _ => True) (fun X Y => Y :^: X)
           (fun X Y Z g f => fun x :e X => g (f x))
           (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f)
           (fun Y => yoneda0 X' 0 Y) (fun Y Z f => yoneda0 X' 1 Y Z f)
	   (fun Y => yoneda1 X X' f Y).
let X. assume HX. let X'. assume HX'. let f. assume Hf.
claim L0: forall X :e Obj, forall Y :e Obj, yoneda0 X 0 Y = Hom Y X.
{ let X. assume HX. let Y. assume HY.
  set yon00 : set := (fun Y :e Obj => Hom Y X).
  set yon01 : set := (fun Z :e Obj => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f).
  prove (yon00,yon01) 0 Y = Hom Y X.
  rewrite tuple_2_0_eq.
  prove yon00 Y = Hom Y X.
  exact beta Obj (fun Y => Hom Y X) Y HY.
}
claim L1: forall X Y Z :e Obj, forall f :e Hom Y Z, yoneda0 X 1 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
{ let X. assume HX. let Y. assume HY. let Z. assume HZ. let f. assume Hf.
  set yon00 : set := (fun Y :e Obj => Hom Y X).
  set yon01 : set := (fun Z :e Obj => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f).
  prove (yon00,yon01) 1 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
  rewrite tuple_2_1_eq.
  prove yon01 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
  rewrite beta Obj (fun Z => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f) Z HZ.
  rewrite beta Obj (fun Y => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f) Y HY.
  exact beta (Hom Y Z) (fun f => fun g :e Hom Z X => comp Y Z X g f) f Hf.
}
claim L2: forall Y :e Obj, yoneda1 X X' f Y = (fun g :e Hom Y X => comp Y X X' f g).
{ let Y. assume HY. exact beta Obj (fun Y => fun g :e Hom Y X => comp Y X X' f g) Y HY. }
set ObjOp : set -> prop := fun Y => Y :e Obj.
set HomOp : set -> set -> set := (fun X Y => Hom Y X).
set ObjSet : set -> prop := fun _ => True.
set HomSet : set -> set -> set := fun X Y => Y :^: X.
set compSet : set -> set -> set -> set -> set -> set := fun X Y Z g f => fun x :e X => g (f x).
set yX0 : set -> set := fun Y => yoneda0 X 0 Y.
set yX1 : set -> set -> set -> set := fun Y Z f => yoneda0 X 1 Y Z f.
set yX'0 : set -> set := fun Y => yoneda0 X' 0 Y.
set yX'1 : set -> set -> set -> set := fun Y Z f => yoneda0 X' 1 Y Z f.
set yf : set -> set := fun Y => yoneda1 X X' f Y.
prove NatTrans ObjOp HomOp ObjSet HomSet compSet yX0 yX1 yX'0 yX'1 yf.
apply SmallCatE Obj Hom id comp HC.
assume HC1 HC2 HC3 HC4 HC5.
apply NatTransI.
- prove forall Y, ObjOp Y -> yf Y :e HomSet (yX0 Y) (yX'0 Y).
  let Y. assume HY: Y :e Obj.
  prove yoneda1 X X' f Y :e yX'0 Y :^: yX0 Y.
  rewrite L2 Y HY.
  prove (fun g :e Hom Y X => comp Y X X' f g) :e Pi_ _ :e yX0 Y, yX'0 Y.
  prove (fun g :e Hom Y X => comp Y X X' f g) :e Pi_ _ :e yoneda0 X 0 Y, yX'0 Y.
  rewrite L0 X HX Y HY.
  prove (fun g :e Hom Y X => comp Y X X' f g) :e Pi_ _ :e Hom Y X, yX'0 Y.
  apply lam_Pi.
  let g. assume Hg: g :e Hom Y X.
  prove comp Y X X' f g :e yX'0 Y.
  prove comp Y X X' f g :e yoneda0 X' 0 Y.
  rewrite L0 X' HX' Y HY.
  prove comp Y X X' f g :e Hom Y X'.
  exact HC2 Y HY X HX X' HX' g Hg f Hf.
- prove forall Y, ObjOp Y -> forall Z, ObjOp Z -> forall h :e HomOp Y Z,
            compSet (yX0 Y) (yX0 Z) (yX'0 Z) (yf Z) (yX1 Y Z h)
          = compSet (yX0 Y) (yX'0 Y) (yX'0 Z) (yX'1 Y Z h) (yf Y).
  let Y. assume HY: Y :e Obj.
  let Z. assume HZ: Z :e Obj.
  let h. assume Hh: h :e Hom Z Y.
  prove (fun k :e yX0 Y => yf Z (yX1 Y Z h k))
      = (fun k :e yX0 Y => yX'1 Y Z h (yf Y k)).
  prove (fun k :e yoneda0 X 0 Y => yf Z (yX1 Y Z h k))
      = (fun k :e yoneda0 X 0 Y => yX'1 Y Z h (yf Y k)).
  rewrite L0 X HX Y HY.
  prove (fun k :e Hom Y X => yf Z (yX1 Y Z h k))
      = (fun k :e Hom Y X => yX'1 Y Z h (yf Y k)).
  apply lam_ext.
  let k. assume Hk: k :e Hom Y X.
  prove yf Z (yX1 Y Z h k) = yX'1 Y Z h (yf Y k).
  prove yoneda1 X X' f Z (yoneda0 X 1 Y Z h k) = yoneda0 X' 1 Y Z h (yoneda1 X X' f Y k).
  transitivity yoneda1 X X' f Z (comp Z Y X k h),
               comp Z X X' f (comp Z Y X k h),
	       comp Z Y X' (comp Y X X' f k) h,
               yoneda0 X' 1 Y Z h (comp Y X X' f k).
  + f_equal.
    prove yoneda0 X 1 Y Z h k = comp Z Y X k h.
    rewrite L1 X HX Z HZ Y HY h Hh.
    prove (fun g :e Hom Y X => comp Z Y X g h) k = comp Z Y X k h.
    exact beta (Hom Y X) (fun g => comp Z Y X g h) k Hk.
  + prove yoneda1 X X' f Z (comp Z Y X k h) = comp Z X X' f (comp Z Y X k h).
    rewrite L2 Z HZ.
    prove (fun g :e Hom Z X => comp Z X X' f g) (comp Z Y X k h) = comp Z X X' f (comp Z Y X k h).
    apply beta.
    prove comp Z Y X k h :e Hom Z X.
    exact HC2 Z HZ Y HY X HX h Hh k Hk.
  + symmetry. exact HC5 Z HZ Y HY X HX X' HX' h Hh k Hk f Hf.
  + prove comp Z Y X' (comp Y X X' f k) h = yoneda0 X' 1 Y Z h (comp Y X X' f k).
    rewrite L1 X' HX' Z HZ Y HY h Hh.
    prove comp Z Y X' (comp Y X X' f k) h = (fun g :e Hom Y X' => comp Z Y X' g h) (comp Y X X' f k).
    symmetry.
    prove (fun g :e Hom Y X' => comp Z Y X' g h) (comp Y X X' f k) = comp Z Y X' (comp Y X X' f k) h.
    apply beta (Hom Y X') (fun g => comp Z Y X' g h) (comp Y X X' f k).
    prove comp Y X X' f k :e Hom Y X'.
    exact HC2 Y HY X HX X' HX' k Hk f Hf.
  + f_equal.
    prove comp Y X X' f k = yoneda1 X X' f Y k.
    rewrite L2 Y HY.
    symmetry.
    prove (fun g :e Hom Y X => comp Y X X' f g) k = comp Y X X' f k.
    apply beta.
    exact Hk.
Qed.

Theorem yoneda_Functor :
  Functor (fun X => X :e Obj) Hom id comp
    (fun F => Presheaf (fun X => X :e Obj) Hom id comp
                       (fun X => F 0 X) (fun X Y f => F 1 X Y f))
    (fun F G => {eta :e Pi_ X :e Obj, G 0 X :^: F 0 X |
                  NatTrans (fun X => X :e Obj) (fun X Y => Hom Y X) (fun _ => True) (fun X Y => Y :^: X) (fun X Y Z g f => fun x :e X => g (f x))
                           (fun X => F 0 X) (fun X Y f => F 1 X Y f)
                           (fun X => G 0 X) (fun X Y f => G 1 X Y f)
                           (fun X => eta X)})
    (fun F => fun X :e Obj => fun x :e F 0 X => x)
    (fun F G H xi eta => fun X :e Obj => fun x :e F 0 X => xi X (eta X x))
    yoneda0 yoneda1.
apply FunctorI.
-
admit.
-
admit.
-
admit.
-
admit.
Qed.

Theorem yoneda1_id : forall X X' :e Obj, forall f :e Hom X X',
   yoneda1 X X' f X (id X) = f.
let X. assume HX. let X'. assume HX'. let f. assume Hf.
apply SmallCatE Obj Hom id comp HC.
assume HC1 HC2 HC3 HC4 HC5.
prove (fun Y :e Obj => fun g :e Hom Y X => comp Y X X' f g) X (id X) = f.
rewrite beta Obj (fun Y => fun g :e Hom Y X => comp Y X X' f g) X HX.
prove (fun g :e Hom X X => comp X X X' f g) (id X) = f.
rewrite beta (Hom X X) (fun g => comp X X X' f g) (id X) (HC1 X HX).
prove comp X X X' f (id X) = f.
exact HC3 X HX X' HX' f Hf.
Qed.

Theorem yoneda1_inj : forall X X' :e Obj, forall f f' :e Hom X X',
    yoneda1 X X' f = yoneda1 X X' f'
 -> f = f'.
let X. assume HX. let X'. assume HX'. let f. assume Hf. let f'. assume Hf'.
assume H1: yoneda1 X X' f = yoneda1 X X' f'.
prove f = f'.
rewrite <- yoneda1_id X HX X' HX' f Hf.
rewrite H1.
exact yoneda1_id X HX X' HX' f' Hf'.
Qed.

Theorem yoneda1_lemma : forall X :e Obj,
  forall P,
    Presheaf (fun Y => Y :e Obj) Hom id comp
             (fun X => P 0 X) (fun X Y f => P 1 X Y f)
  ->
  forall eta :e {eta :e Pi_ Y :e Obj, P 0 Y :^: yoneda0 X 0 Y |
                    NatTrans (fun Y => Y :e Obj) (fun Y Z => Hom Z Y)
		             (fun _ => True) (fun Y Z => Z :^: Y) (fun Y Z W g f => fun x :e Y => g (f x))
                             (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f)
                             (fun Y => P 0 Y) (fun Y Z f => P 1 Y Z f)
                             (fun Y => eta Y)},
  eta = (fun Y :e Obj => fun f :e Hom Y X => P 1 X Y f (eta X (id X))).
let X. assume HX.
let P.
assume HP: Presheaf (fun Y => Y :e Obj) Hom id comp
                    (fun X => P 0 X) (fun X Y f => P 1 X Y f).
let eta.
assume Heta.
apply HP.
assume HP1: forall Y :e Obj, True.
assume HP2: forall Y Z :e Obj, forall h :e Hom Z Y, P 1 Y Z h :e P 0 Z :^: P 0 Y.
assume HP3: forall Y :e Obj, P 1 Y Y (id Y) = fun y :e P 0 Y => y.
assume HP4: forall Y Z W :e Obj, forall g :e Hom W Z, forall h :e Hom Z Y,
              P 1 Y W (comp W Z Y h g) = fun y :e P 0 Y => P 1 Z W g (P 1 Y Z h y).
apply SepE (Pi_ Y :e Obj, P 0 Y :^: yoneda0 X 0 Y)
           (fun eta =>
             NatTrans (fun Y => Y :e Obj) (fun Y Z => Hom Z Y)
	              (fun _ => True) (fun Y Z => Z :^: Y) (fun Y Z W g f => fun x :e Y => g (f x))
                      (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f)
                      (fun Y => P 0 Y) (fun Y Z f => P 1 Y Z f)
                      (fun Y => eta Y))
           eta Heta.
assume Heta1: eta :e Pi_ Y :e Obj, P 0 Y :^: yoneda0 X 0 Y.
assume Heta2: NatTrans (fun Y => Y :e Obj) (fun Y Z => Hom Z Y) (fun _ => True) (fun Y Z => Z :^: Y) (fun Y Z W g f => fun x :e Y => g (f x))
                      (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f)
                      (fun Y => P 0 Y) (fun Y Z f => P 1 Y Z f)
                      (fun Y => eta Y).
apply Heta2.
assume Heta3: forall Y :e Obj, eta Y :e P 0 Y :^: yoneda0 X 0 Y.
assume Heta4: forall Y Z :e Obj, forall h :e Hom Z Y,
                  (fun g :e yoneda0 X 0 Y => eta Z (yoneda0 X 1 Y Z h g))
                = (fun g :e yoneda0 X 0 Y => P 1 Y Z h (eta Y g)).
apply SmallCatE Obj Hom id comp HC.
assume HC1 HC2 HC3 HC4 HC5.
set yon00 : set := (fun Y :e Obj => Hom Y X).
set yon01 : set := (fun Z :e Obj => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f).
claim L0: forall Y :e Obj, yoneda0 X 0 Y = Hom Y X.
{ let Y. assume HY.
  prove (yon00,yon01) 0 Y = Hom Y X.
  rewrite tuple_2_0_eq.
  prove yon00 Y = Hom Y X.
  exact beta Obj (fun Y => Hom Y X) Y HY.
}
claim L1: forall Y Z :e Obj, forall f :e Hom Y Z, yoneda0 X 1 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
{ let Y. assume HY. let Z. assume HZ. let f. assume Hf.
  prove (yon00,yon01) 1 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
  rewrite tuple_2_1_eq.
  prove yon01 Z Y f = (fun g :e Hom Z X => comp Y Z X g f).
  rewrite beta Obj (fun Z => fun Y :e Obj => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f) Z HZ.
  rewrite beta Obj (fun Y => fun f :e Hom Y Z => fun g :e Hom Z X => comp Y Z X g f) Y HY.
  exact beta (Hom Y Z) (fun f => fun g :e Hom Z X => comp Y Z X g f) f Hf.
}
claim L2: forall Y Z :e Obj, forall f :e Hom Z Y, yoneda0 X 1 Y Z f :e (Hom Z X) :^: (Hom Y X).
{ let Y. assume HY. let Z. assume HZ.
  let f. assume Hf: f :e Hom Z Y.
  rewrite L1 Z HZ Y HY f Hf.
  prove (fun g :e Hom Y X => comp Z Y X g f) :e Hom Z X :^: Hom Y X.
  prove (fun g :e Hom Y X => comp Z Y X g f) :e Pi_ g :e Hom Y X, Hom Z X.
  apply lam_Pi.
  let g. assume Hg: g :e Hom Y X.
  prove comp Z Y X g f :e Hom Z X.
  exact HC2 Z HZ Y HY X HX f Hf g Hg.
}
claim L3: id X :e yoneda0 X 0 X.
{ rewrite L0 X HX.
  prove id X :e Hom X X.
  exact HC1 X HX.
}
transitivity (fun Y :e Obj => eta Y).
- symmetry. exact Pi_eta Obj (fun Y => P 0 Y :^: yoneda0 X 0 Y) eta Heta1.
- apply lam_ext. let Y. assume HY: Y :e Obj.
  prove eta Y = fun f :e Hom Y X => P 1 X Y f (eta X (id X)).
  transitivity (fun f :e Hom Y X => eta Y f).
  + prove eta Y = (fun f :e Hom Y X => eta Y f).
    rewrite <- L0 Y HY.
    prove eta Y = (fun f :e yoneda0 X 0 Y => eta Y f).
    symmetry.
    exact Pi_eta (yoneda0 X 0 Y) (fun _ => P 0 Y) (eta Y) (Heta3 Y HY).
  + apply lam_ext. let f. assume Hf: f :e Hom Y X.
    claim Lf: f :e yoneda0 X 0 Y.
    { rewrite L0 Y HY. exact Hf. }
    prove eta Y f = P 1 X Y f (eta X (id X)).
    transitivity eta Y (yoneda0 X 1 X Y f (id X)).
    * prove eta Y f = eta Y (yoneda0 X 1 X Y f (id X)).
      rewrite L1 Y HY X HX f Hf.
      prove eta Y f = eta Y ((fun g :e Hom X X => comp Y X X g f) (id X)).
      f_equal.
      prove f = (fun g :e Hom X X => comp Y X X g f) (id X).
      rewrite beta (Hom X X) (fun g => comp Y X X g f) (id X) (HC1 X HX).
      prove f = comp Y X X (id X) f.
      symmetry.
      exact HC4 Y HY X HX f Hf.
    * prove eta Y (yoneda0 X 1 X Y f (id X)) = P 1 X Y f (eta X (id X)).
      rewrite <- beta (yoneda0 X 0 X) (fun g => eta Y (yoneda0 X 1 X Y f g)) (id X) L3.
      prove (fun g :e yoneda0 X 0 X => eta Y (yoneda0 X 1 X Y f g)) (id X)
          = P 1 X Y f (eta X (id X)).
      rewrite <- beta (yoneda0 X 0 X) (fun g => P 1 X Y f (eta X g)) (id X) L3.
      prove (fun g :e yoneda0 X 0 X => eta Y (yoneda0 X 1 X Y f g)) (id X)
          = (fun g :e yoneda0 X 0 X => P 1 X Y f (eta X g)) (id X).
      f_equal.
      exact Heta4 X HX Y HY f Hf.
Qed.

(**
Theorem yoneda1_lemma_rr : forall X X' :e Obj, forall f :e Hom X X',
  forall eta :e {eta :e Pi_ Y :e Obj, yoneda0 X' 0 Y :^: yoneda0 X 0 Y |
                    NatTrans (fun Y => Y :e Obj) (fun Y Z => Hom Y Z)
		             (fun _ => True) (fun Y Z => Z :^: Y) (fun Y Z W g f => fun x :e Y => g (f x))
                             (fun Y => yoneda0 X 0 Y) (fun Y Z f => yoneda0 X 1 Y Z f)
                             (fun Y => yoneda0 X' 0 Y) (fun Y Z f => yoneda0 X' 1 Y Z f)
                             (fun Y => eta Y)},
  True.    
admit.
Qed.
**)

End Yoneda.
