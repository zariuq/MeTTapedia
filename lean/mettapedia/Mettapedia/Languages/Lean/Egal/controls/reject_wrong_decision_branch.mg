(** The conjunction of a true and a false decision cannot select isTrue. **)
Theorem reject_wrong_decision_branch : forall p q :e LeanProp,
  0 :e p -> (0 :e q -> False) ->
  Lean_instDecidableAnd p q (Lean_Decidable_isTrue_node p 0)
    (Lean_Decidable_isFalse_node q 0) = Lean_Decidable_isTrue_node (Lean_And_Prop p q) 0.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
assume Hyes: 0 :e p. assume Hno: 0 :e q -> False.
exact Lean_instDecidableAnd_eq_2 p Hp q Hq Hyes Hno.
Qed.
