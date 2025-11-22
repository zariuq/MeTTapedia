Theorem cases_10 : forall i :e 10, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p i.
let i. assume Hi: i :e 10.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9.
apply ordsuccE 9 i Hi.
- assume Hi9: i :e 9.
  exact cases_9 i Hi9 p H0 H1 H2 H3 H4 H5 H6 H7 H8.
- assume Heq: i = 9.
  rewrite Heq. exact H9.
Qed.

Theorem cases_11 : forall i :e 11, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p i.
let i. assume Hi: i :e 11.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10.
apply ordsuccE 10 i Hi.
- assume Hi10: i :e 10.
  exact cases_10 i Hi10 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
- assume Heq: i = 10.
  rewrite Heq. exact H10.
Qed.

Theorem cases_12 : forall i :e 12, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p i.
let i. assume Hi: i :e 12.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
apply ordsuccE 11 i Hi.
- assume Hi11: i :e 11.
  exact cases_11 i Hi11 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
- assume Heq: i = 11.
  rewrite Heq. exact H11.
Qed.

Theorem cases_13 : forall i :e 13, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p 12 -> p i.
let i. assume Hi: i :e 13.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
assume H12: p 12.
apply ordsuccE 12 i Hi.
- assume Hi12: i :e 12.
  exact cases_12 i Hi12 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
- assume Heq: i = 12.
  rewrite Heq. exact H12.
Qed.

Theorem cases_14 : forall i :e 14, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p 12 -> p 13 -> p i.
let i. assume Hi: i :e 14.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
assume H12: p 12. assume H13: p 13.
apply ordsuccE 13 i Hi.
- assume Hi13: i :e 13.
  exact cases_13 i Hi13 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
- assume Heq: i = 13.
  rewrite Heq. exact H13.
Qed.

Theorem cases_15 : forall i :e 15, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p 12 -> p 13 -> p 14 -> p i.
let i. assume Hi: i :e 15.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
assume H12: p 12. assume H13: p 13. assume H14: p 14.
apply ordsuccE 14 i Hi.
- assume Hi14: i :e 14.
  exact cases_14 i Hi14 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
- assume Heq: i = 14.
  rewrite Heq. exact H14.
Qed.

Theorem cases_16 : forall i :e 16, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p 12 -> p 13 -> p 14 -> p 15 -> p i.
let i. assume Hi: i :e 16.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
assume H12: p 12. assume H13: p 13. assume H14: p 14. assume H15: p 15.
apply ordsuccE 15 i Hi.
- assume Hi15: i :e 15.
  exact cases_15 i Hi15 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
- assume Heq: i = 15.
  rewrite Heq. exact H15.
Qed.

Theorem cases_17 : forall i :e 17, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p 12 -> p 13 -> p 14 -> p 15 -> p 16 -> p i.
let i. assume Hi: i :e 17.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
assume H12: p 12. assume H13: p 13. assume H14: p 14. assume H15: p 15.
assume H16: p 16.
apply ordsuccE 16 i Hi.
- assume Hi16: i :e 16.
  exact cases_16 i Hi16 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
- assume Heq: i = 16.
  rewrite Heq. exact H16.
Qed.

Theorem cases_18 : forall i :e 18, forall p:set->prop,
  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p 9 -> p 10 -> p 11 -> p 12 -> p 13 -> p 14 -> p 15 -> p 16 -> p 17 -> p i.
let i. assume Hi: i :e 18.
let p: set -> prop.
assume H0: p 0. assume H1: p 1. assume H2: p 2. assume H3: p 3.
assume H4: p 4. assume H5: p 5. assume H6: p 6. assume H7: p 7.
assume H8: p 8. assume H9: p 9. assume H10: p 10. assume H11: p 11.
assume H12: p 12. assume H13: p 13. assume H14: p 14. assume H15: p 15.
assume H16: p 16. assume H17: p 17.
apply ordsuccE 17 i Hi.
- assume Hi17: i :e 17.
  exact cases_17 i Hi17 p H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
- assume Heq: i = 17.
  rewrite Heq. exact H17.
Qed.
