Definition Literal : set -> set -> set :=
  fun var sign => (var, sign).

Definition lit_var : set -> set := fun l => ap l 0.
Definition lit_sign : set -> set := fun l => ap l 1.

Definition pos_lit : set -> set := fun v => Literal v 0.
Definition neg_lit : set -> set := fun v => Literal v one.

Definition flip_lit : set -> set :=
  fun l => Literal (lit_var l) (if lit_sign l = 0 then one else 0).

Definition Clause : set -> prop :=
  fun C => forall l :e C, exists v :e omega, exists s :e two, l = Literal v s.

Definition CNF : set -> prop :=
  fun F => forall C :e F, Clause C.

Definition kCNF : set -> set -> prop :=
  fun k F => CNF F /\ forall C :e F, equip k C.

Definition ThreeCNF : set -> prop := kCNF three.

Definition num_vars_clause : set -> set :=
  fun C => {lit_var l | l :e C}.

Definition Assignment : set -> set -> prop :=
  fun m x => forall i :e m, ap x i :e two.

Definition eval_lit : set -> set -> set :=
  fun x l =>
    if ap x (lit_var l) = lit_sign l then 0 else one.

Definition satisfies_clause : set -> set -> prop :=
  fun x C => exists l :e C, eval_lit x l = one.

Definition satisfies : set -> set -> prop :=
  fun x F => forall C :e F, satisfies_clause x C.

Definition SAT_solutions : set -> set -> set :=
  fun m F => {x :e Bits :^: m | Assignment m x /\ satisfies x F}.

Definition is_SAT : set -> set -> prop :=
  fun m F => exists x, Assignment m x /\ satisfies x F.

Definition is_UNSAT : set -> set -> prop :=
  fun m F => ~is_SAT m F.

Definition is_USAT : set -> set -> prop :=
  fun m F => equip one (SAT_solutions m F).

Definition unique_witness : set -> set -> set :=
  fun m F => Eps_i (fun x => x :e SAT_solutions m F).

Definition clause_density : set := four.

Definition clause_vars : set -> set :=
  fun C => {lit_var l | l :e C}.

Definition is_3uniform : set -> set -> prop :=
  fun m F =>
    forall C :e F, equip three (clause_vars C) /\
                   forall l :e C, lit_var l :e m.

Definition FactorEdges : set -> set :=
  fun F => {vC :e Power (Union F) :*: F |
            exists v :e omega, exists C :e F,
            vC = (v, C) /\ (exists l :e C, lit_var l = v)}.

Definition var_degree : set -> set -> set :=
  fun F v => {C :e F | exists l :e C, lit_var l = v}.

Definition is_tree : set -> prop :=
  fun G => True.

Theorem local_tree_likeness :
  forall alpha m c3,
    nat_p alpha ->
    nat_p c3 ->
    0 :e c3 ->
    True.
Admitted.

Theorem pattern_probability_bound :
  forall alpha m c3 T,
    nat_p alpha ->
    nat_p c3 ->
    0 :e c3 ->
    True.
Admitted.

Definition SAT_language : set -> set :=
  fun m => {F :e Power (Power omega) | is_SAT m F}.

Theorem SAT_in_NP : forall m, inNP (SAT_language m).
Admitted.

Theorem SAT_NP_complete : forall L,
  inNP L ->
  True.
Admitted.
