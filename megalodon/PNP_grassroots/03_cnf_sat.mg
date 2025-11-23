(* ========================================================================= *)
(* CNF and SAT Formalization                                                 *)
(* Builds on 00_preamble.mg, 01_foundations.mg                               *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Part I: Literals and Signs                                                *)
(* ========================================================================= *)

(* A literal is a pair (variable, sign) where sign ∈ {0,1} *)
(* sign = 0 means positive, sign = 1 means negative *)

Definition Literal : set -> set -> set :=
  fun var sign => pair var sign.

Definition lit_var : set -> set := fun l => ap l 0.
Definition lit_sign : set -> set := fun l => ap l 1.

Definition pos_lit : set -> set := fun v => Literal v 0.
Definition neg_lit : set -> set := fun v => Literal v 1.

(* Flip a literal's sign *)
Definition flip_lit : set -> set :=
  fun l => Literal (lit_var l) (xor (lit_sign l) 1).

(* A literal is well-formed if variable ∈ ω and sign ∈ {0,1} *)
Definition is_literal : set -> set -> prop :=
  fun m l => lit_var l :e m /\ lit_sign l :e Bits.

Theorem pos_lit_is_literal : forall m v, v :e m -> is_literal m (pos_lit v).
let m v. assume Hv: v :e m.
apply andI.
- prove lit_var (pos_lit v) :e m.
  prove ap (pair v 0) 0 :e m.
  rewrite ap_pair_0 v 0.
  exact Hv.
- prove lit_sign (pos_lit v) :e Bits.
  prove ap (pair v 0) 1 :e Bits.
  rewrite ap_pair_1 v 0.
  exact In_0_2.
Qed.

Theorem neg_lit_is_literal : forall m v, v :e m -> is_literal m (neg_lit v).
let m v. assume Hv: v :e m.
apply andI.
- prove lit_var (neg_lit v) :e m.
  prove ap (pair v 1) 0 :e m.
  rewrite ap_pair_0 v 1.
  exact Hv.
- prove lit_sign (neg_lit v) :e Bits.
  prove ap (pair v 1) 1 :e Bits.
  rewrite ap_pair_1 v 1.
  exact In_1_2.
Qed.

(* ========================================================================= *)
(* Part II: Clauses                                                          *)
(* ========================================================================= *)

(* A clause is a finite set of literals (disjunction) *)
Definition is_clause : set -> set -> prop :=
  fun m C => forall l :e C, is_literal m l.

(* Empty clause (always false) *)
Definition empty_clause : set := Empty.

Theorem empty_clause_is_clause : forall m, is_clause m empty_clause.
let m.
let l. assume Hl: l :e empty_clause.
prove is_literal m l.
apply False_rect.
exact (EmptyE l Hl).
Qed.

(* ========================================================================= *)
(* Part III: CNF Formulas                                                    *)
(* ========================================================================= *)

(* A CNF formula is a set of clauses (conjunction of disjunctions) *)
Definition is_CNF : set -> set -> prop :=
  fun m F => forall C :e F, is_clause m C.

(* k-CNF: each clause has exactly k literals *)
Definition is_kCNF : set -> set -> set -> prop :=
  fun k m F => is_CNF m F /\ forall C :e F, equip k C.

Definition is_3CNF : set -> set -> prop := is_kCNF 3.

(* Empty formula (always true, vacuously satisfied) *)
Definition empty_CNF : set := Empty.

Theorem empty_CNF_is_CNF : forall m, is_CNF m empty_CNF.
let m.
let C. assume HC: C :e empty_CNF.
apply False_rect.
exact (EmptyE C HC).
Qed.

(* ========================================================================= *)
(* Part IV: Assignments and Evaluation                                       *)
(* ========================================================================= *)

(* An assignment over m variables is a function m -> {0,1} *)
Definition is_assignment : set -> set -> prop :=
  fun m x => forall i :e m, ap x i :e Bits.

(* Evaluate a literal under an assignment *)
(* Returns 1 (true) if variable value matches expected value for satisfaction *)
(* For positive literal (sign=0): satisfied if x[v] = 1 *)
(* For negative literal (sign=1): satisfied if x[v] = 0 *)
Definition eval_lit : set -> set -> set :=
  fun x l =>
    let v := lit_var l in
    let s := lit_sign l in
    (* positive (s=0): satisfied when x[v]=1, i.e., xor x[v] s = 1 *)
    (* negative (s=1): satisfied when x[v]=0, i.e., xor x[v] s = 1 *)
    xor (ap x v) s.

(* A clause is satisfied if at least one literal evaluates to 1 *)
Definition satisfies_clause : set -> set -> prop :=
  fun x C => exists l :e C, eval_lit x l = 1.

(* A CNF formula is satisfied if all clauses are satisfied *)
Definition satisfies : set -> set -> prop :=
  fun x F => forall C :e F, satisfies_clause x C.

(* The set of satisfying assignments *)
Definition SAT_solutions : set -> set -> set :=
  fun m F => {x :e Bits :^: m | is_assignment m x /\ satisfies x F}.

(* ========================================================================= *)
(* Part V: SAT, UNSAT, USAT Predicates                                       *)
(* ========================================================================= *)

(* Formula is satisfiable *)
Definition is_SAT : set -> set -> prop :=
  fun m F => exists x, is_assignment m x /\ satisfies x F.

(* Formula is unsatisfiable *)
Definition is_UNSAT : set -> set -> prop :=
  fun m F => ~is_SAT m F.

(* Formula has a unique satisfying assignment *)
Definition is_USAT : set -> set -> prop :=
  fun m F => equip 1 (SAT_solutions m F).

(* The unique witness (when it exists) *)
Definition unique_witness : set -> set -> set :=
  fun m F => Eps_i (fun x => x :e SAT_solutions m F).

(* ========================================================================= *)
(* Part VI: Basic Properties                                                 *)
(* ========================================================================= *)

(* Empty formula is always satisfiable *)
Theorem empty_CNF_is_SAT : forall m :e omega, is_SAT m empty_CNF.
let m. assume Hm: m :e omega.
prove exists x, is_assignment m x /\ satisfies x empty_CNF.
(* The zero assignment satisfies the empty formula *)
claim Hzero: is_assignment m (zero_vector m).
{ let i. assume Hi: i :e m.
  prove ap (zero_vector m) i :e Bits.
  rewrite beta m (fun _ => 0) i Hi.
  exact In_0_2. }
claim Hsat: satisfies (zero_vector m) empty_CNF.
{ let C. assume HC: C :e empty_CNF.
  apply False_rect.
  exact (EmptyE C HC). }
apply (fun P f x => f x). exact (zero_vector m).
apply andI.
- exact Hzero.
- exact Hsat.
Qed.

(* Formula containing empty clause is unsatisfiable *)
Theorem empty_clause_makes_UNSAT : forall m F,
  empty_clause :e F -> is_UNSAT m F.
let m F. assume Hempty: empty_clause :e F.
prove ~is_SAT m F.
assume Hsat: is_SAT m F.
apply Hsat. let x. assume Hx: is_assignment m x /\ satisfies x F.
apply Hx. assume _ Hxsat: satisfies x F.
claim H: satisfies_clause x empty_clause.
{ exact (Hxsat empty_clause Hempty). }
prove False.
apply H. let l. assume Hl: l :e empty_clause /\ eval_lit x l = 1.
apply Hl. assume Hle: l :e empty_clause. assume _.
exact (EmptyE l Hle).
Qed.

(* ========================================================================= *)
(* Part VII: Random 3-CNF Parameters                                         *)
(* ========================================================================= *)

(* Clause density α: ratio of clauses to variables *)
(* For random 3-SAT, α ≈ 4.267 is the satisfiability threshold *)
Parameter clause_density_alpha : set.
Axiom alpha_positive : 0 :e clause_density_alpha.

(* Number of clauses in a random (α,m)-3CNF: α*m *)
Definition num_clauses : set -> set :=
  fun m => clause_density_alpha * m.

(* ========================================================================= *)
(* Part VIII: Variable Graph Structure                                       *)
(* ========================================================================= *)

(* Variables appearing in a clause *)
Definition clause_vars : set -> set :=
  fun C => {lit_var l | l :e C}.

(* The factor graph of a CNF: bipartite graph (variables, clauses, edges) *)
(* Edge (v, C) exists iff variable v appears in clause C *)
Definition factor_edges : set -> set :=
  fun F => {(v, C) | C :e F, exists l :e C, lit_var l = v}.

(* Degree of a variable: number of clauses containing it *)
Definition var_degree : set -> set -> set :=
  fun F v => {C :e F | exists l :e C, lit_var l = v}.

(* r-neighborhood: clauses within distance r from a variable *)
(* (Requires graph infrastructure) *)

(* ========================================================================= *)
(* Part IX: SAT Language and Complexity                                      *)
(* ========================================================================= *)

(* SAT as a language (set of satisfiable formulas) *)
Definition SAT_language : set -> set :=
  fun m => {F :e Power (Power omega) | is_SAT m F}.

(* 3-SAT language *)
Definition ThreeSAT_language : set -> set :=
  fun m => {F :e Power (Power omega) | is_3CNF m F /\ is_SAT m F}.

(* ========================================================================= *)
(* SAT Complexity Results                                                    *)
(* ========================================================================= *)
(* These are fundamental complexity-theoretic results. See 01_foundations.mg *)
(* for the full Cook-Levin citation.                                          *)
(* ========================================================================= *)

(* SAT ∈ NP: Nondeterministically guess assignment, verify in O(|F|·m) *)
(* Verification: iterate through clauses, check each has a true literal. *)
Axiom SAT_in_NP : forall m :e omega, inNP (SAT_language m).

(* Cook-Levin Theorem: SAT is NP-complete *)
(* Source: Cook (1971), Levin (1973) - see 01_foundations.mg for full citation *)
(* This concrete version works with SAT_language over m variables. *)
Axiom Cook_Levin : forall m :e omega, NP_complete (SAT_language m).

(* 3-SAT is NP-complete by reduction from SAT *)
(* Source: Karp, R.M. (1972). "Reducibility among combinatorial problems". *)
(*         In: Complexity of Computer Computations, Plenum Press, 85-103.    *)
(* The reduction replaces each clause (l₁ ∨ ... ∨ lₖ) with k > 3 by:        *)
(* (l₁ ∨ l₂ ∨ y₁) ∧ (¬y₁ ∨ l₃ ∨ y₂) ∧ ... ∧ (¬yₖ₋₃ ∨ lₖ₋₁ ∨ lₖ)         *)
(* using fresh auxiliary variables y₁, ..., yₖ₋₃.                           *)
Axiom ThreeSAT_NP_complete : forall m :e omega, NP_complete (ThreeSAT_language m).

