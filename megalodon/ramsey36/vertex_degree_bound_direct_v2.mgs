% Direct proof: vertex with 6 neighbors in triangle-free graph contradicts no_6_indep
%
% Strategy: Apply no_6_indep to {n1,n2,n3,n4,n5,n6}, get disjunction of edges.
% Use triangle-free to show each edge leads to contradiction.

Theorem vertex_6_neighbors_contradiction:
  forall R : set -> set -> prop,
  forall V : set,
  forall v n1 n2 n3 n4 n5 n6 : set,
  (forall x y :e V, R x y -> R y x) ->
  (forall x y z :e V, R x y -> R y z -> R x z -> False) ->
  (forall a b c d e f :e V,
    a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
    b <> c -> b <> d -> b <> e -> b <> f ->
    c <> d -> c <> e -> c <> f ->
    d <> e -> d <> f ->
    e <> f ->
    (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
     R b c \/ R b d \/ R b e \/ R b f \/
     R c d \/ R c e \/ R c f \/
     R d e \/ R d f \/
     R e f)) ->
  v :e V -> n1 :e V -> n2 :e V -> n3 :e V -> n4 :e V -> n5 :e V -> n6 :e V ->
  n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 ->
  n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 ->
  n3 <> n4 -> n3 <> n5 -> n3 <> n6 ->
  n4 <> n5 -> n4 <> n6 ->
  n5 <> n6 ->
  R v n1 -> R v n2 -> R v n3 -> R v n4 -> R v n5 -> R v n6 ->
  False.
let R V v n1 n2 n3 n4 n5 n6.
assume Hsym : forall x y :e V, R x y -> R y x.
assume Htf : forall x y z :e V, R x y -> R y z -> R x z -> False.
assume Hno6 : forall a b c d e f :e V,
  a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
  b <> c -> b <> d -> b <> e -> b <> f ->
  c <> d -> c <> e -> c <> f ->
  d <> e -> d <> f ->
  e <> f ->
  (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
   R b c \/ R b d \/ R b e \/ R b f \/
   R c d \/ R c e \/ R c f \/
   R d e \/ R d f \/
   R e f).
assume Hv : v :e V.
assume Hn1 : n1 :e V.
assume Hn2 : n2 :e V.
assume Hn3 : n3 :e V.
assume Hn4 : n4 :e V.
assume Hn5 : n5 :e V.
assume Hn6 : n6 :e V.
assume Hd12 : n1 <> n2.
assume Hd13 : n1 <> n3.
assume Hd14 : n1 <> n4.
assume Hd15 : n1 <> n5.
assume Hd16 : n1 <> n6.
assume Hd23 : n2 <> n3.
assume Hd24 : n2 <> n4.
assume Hd25 : n2 <> n5.
assume Hd26 : n2 <> n6.
assume Hd34 : n3 <> n4.
assume Hd35 : n3 <> n5.
assume Hd36 : n3 <> n6.
assume Hd45 : n4 <> n5.
assume Hd46 : n4 <> n6.
assume Hd56 : n5 <> n6.
assume Hvn1 : R v n1.
assume Hvn2 : R v n2.
assume Hvn3 : R v n3.
assume Hvn4 : R v n4.
assume Hvn5 : R v n5.
assume Hvn6 : R v n6.
claim Ledge : R n1 n2 \/ R n1 n3 \/ R n1 n4 \/ R n1 n5 \/ R n1 n6 \/ R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6.
{ exact (Hno6 n1 n2 n3 n4 n5 n6 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hd12 Hd13 Hd14 Hd15 Hd16 Hd23 Hd24 Hd25 Hd26 Hd34 Hd35 Hd36 Hd45 Hd46 Hd56). }
claim C12 : R n1 n2 -> False.
{ assume H12. exact (Htf v n1 n2 Hv Hn1 Hn2 Hvn1 H12 Hvn2). }
claim C13 : R n1 n3 -> False.
{ assume H13. exact (Htf v n1 n3 Hv Hn1 Hn3 Hvn1 H13 Hvn3). }
claim C14 : R n1 n4 -> False.
{ assume H14. exact (Htf v n1 n4 Hv Hn1 Hn4 Hvn1 H14 Hvn4). }
claim C15 : R n1 n5 -> False.
{ assume H15. exact (Htf v n1 n5 Hv Hn1 Hn5 Hvn1 H15 Hvn5). }
claim C16 : R n1 n6 -> False.
{ assume H16. exact (Htf v n1 n6 Hv Hn1 Hn6 Hvn1 H16 Hvn6). }
claim C23 : R n2 n3 -> False.
{ assume H23. exact (Htf v n2 n3 Hv Hn2 Hn3 Hvn2 H23 Hvn3). }
claim C24 : R n2 n4 -> False.
{ assume H24. exact (Htf v n2 n4 Hv Hn2 Hn4 Hvn2 H24 Hvn4). }
claim C25 : R n2 n5 -> False.
{ assume H25. exact (Htf v n2 n5 Hv Hn2 Hn5 Hvn2 H25 Hvn5). }
claim C26 : R n2 n6 -> False.
{ assume H26. exact (Htf v n2 n6 Hv Hn2 Hn6 Hvn2 H26 Hvn6). }
claim C34 : R n3 n4 -> False.
{ assume H34. exact (Htf v n3 n4 Hv Hn3 Hn4 Hvn3 H34 Hvn4). }
claim C35 : R n3 n5 -> False.
{ assume H35. exact (Htf v n3 n5 Hv Hn3 Hn5 Hvn3 H35 Hvn5). }
claim C36 : R n3 n6 -> False.
{ assume H36. exact (Htf v n3 n6 Hv Hn3 Hn6 Hvn3 H36 Hvn6). }
claim C45 : R n4 n5 -> False.
{ assume H45. exact (Htf v n4 n5 Hv Hn4 Hn5 Hvn4 H45 Hvn5). }
claim C46 : R n4 n6 -> False.
{ assume H46. exact (Htf v n4 n6 Hv Hn4 Hn6 Hvn4 H46 Hvn6). }
claim C56 : R n5 n6 -> False.
{ assume H56. exact (Htf v n5 n6 Hv Hn5 Hn6 Hvn5 H56 Hvn6). }
apply orE (R n1 n2) (R n1 n3 \/ R n1 n4 \/ R n1 n5 \/ R n1 n6 \/ R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ Ledge.
- exact C12.
- assume L13.
  apply orE (R n1 n3) (R n1 n4 \/ R n1 n5 \/ R n1 n6 \/ R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L13.
  + exact C13.
  + assume L14.
    apply orE (R n1 n4) (R n1 n5 \/ R n1 n6 \/ R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L14.
    * exact C14.
    * assume L15.
      apply orE (R n1 n5) (R n1 n6 \/ R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L15.
      -- exact C15.
      -- assume L16.
         apply orE (R n1 n6) (R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L16.
         ** exact C16.
         ** assume L23.
            apply orE (R n2 n3) (R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L23.
            --- exact C23.
            --- assume L24.
                apply orE (R n2 n4) (R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L24.
                ++ exact C24.
                ++ assume L25.
                   apply orE (R n2 n5) (R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L25.
                   ** exact C25.
                   ** assume L26.
                      apply orE (R n2 n6) (R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L26.
                      --- exact C26.
                      --- assume L34.
                          apply orE (R n3 n4) (R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L34.
                          ++ exact C34.
                          ++ assume L35.
                             apply orE (R n3 n5) (R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L35.
                             ** exact C35.
                             ** assume L36.
                                apply orE (R n3 n6) (R n4 n5 \/ R n4 n6 \/ R n5 n6) False _ _ L36.
                                --- exact C36.
                                --- assume L45.
                                    apply orE (R n4 n5) (R n4 n6 \/ R n5 n6) False _ _ L45.
                                    ++ exact C45.
                                    ++ assume L46.
                                       apply orE (R n4 n6) (R n5 n6) False _ _ L46.
                                       ** exact C46.
                                       ** exact C56.
Qed.
