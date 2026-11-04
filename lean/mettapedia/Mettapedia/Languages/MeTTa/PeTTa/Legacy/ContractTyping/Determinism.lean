import Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping.Contract
import Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping.Coverage
import Mettapedia.Languages.MeTTa.PeTTa.CheckedCardinality

/-!
# Determinism grades of function bodies (`lib_det`)

A call checks its arguments against the callee's declared types and its answers against the
declared result. A `-[det]->` or `-[semidet]->` function commits to its first matching clause;
any other runs every matching clause. Evaluation has fuel (partial correctness). `infer` grades
syntax with `AnswerCardinality` (`lib_det`'s `seq`, `choice`, `join`, `once_grade`),
assume-guarantee: a callee has its declared grade; a partial application is one value; a call
through a parameter declared with an arrow has that arrow's grade, another closure call any; a
lambda is a function graded by its body. Patterns of `let` and `case`, and a committing
function's heads, cannot fail where a sound coverage test (`Coverage.lean`) says they cover the
declared type. `det_validation_sound`: if every function validates, every answer list of a call
is allowed by the callee's declaration. Effect-polymorphic arrows `-[$e]->` are not modelled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping

open Mettapedia.Machines.AnswerCardinality
open Mettapedia.Languages.MeTTa.PeTTa.CheckedCardinality (Declaration validates validates_iff)

inductive Expr where
  | lit (t : Term)
  /-- A parameter or a bound value, by its index in the environment. -/
  | var (i : Nat)
  | arith (op : Term → Term → Term) (a b : Expr)
  | call (f : String) (args : List Expr)
  /-- `(f X₁ .. Xₖ)` with fewer arguments than `f` takes: one closure per argument choice. -/
  | papp (f : String) (args : List Expr)
  /-- A call through the closure held in the environment. -/
  | callVar (i : Nat) (args : List Expr)
  | superpose (es : List Expr)
  /-- `match` against a space: any number of answers. -/
  | space (query : List Term → List Term)
  | if3 (cond yes no : Expr)
  | if2 (cond yes : Expr)
  /-- `(let P E B)`: a value of `E` that `P` does not match gives no answer. -/
  | let_ (p : Pat) (e body : Expr)
  /-- `case`: the first branch whose pattern matches the value, with the value bound. -/
  | case (scrut : Expr) (branches : List (Pat × Expr))
  | once (e : Expr)
  | collapse (e : Expr)

structure Clause where
  head : List Pat
  body : Expr

structure Fn where
  /-- Each parameter's declared type, and the determinism of its arrow if it is one. -/
  params : List (Ty × Option Declaration)
  res : Ty
  clauses : List Clause
  /-- `-[det]->` and `-[semidet]->` commit to the first clause whose head matches. -/
  commits : Bool

def Fn.types (fn : Fn) : List Ty := fn.params.map Prod.fst

/-- What the analysis knows of a value of the environment: its declared type and, for a
closure, its declared grade. -/
abbrev Slot := Option Ty × Option Grade

def Fn.slots (fn : Fn) : List Slot := fn.params.map fun p => (some p.1, p.2.map Declaration.grade)

/-- A closure: a function's name, or its partial application. -/
def Term.closure? : Term → Option (String × List Term)
  | .sym g => some (g, [])
  | .app (.sym g :: bs) => some (g, bs)
  | _ => none

/-! ## Grades -/

def joinAll : List Grade → Grade
  | [] => .zero
  | [g] => g
  | g :: gs => join g (joinAll gs)

variable {sig : Sig} (cover : List (List Pat) → List Ty → Bool) (P : String → Fn)
  (D : String → Declaration)

/-- `value_type/2`: a parameter's declared type, or a call's declared result. -/
def valueType (ctx : List Slot) : Expr → Option Ty
  | .var i => (ctx.getD i (none, none)).1
  | .call f _ => some (P f).res
  | _ => none

/-- A variable pattern, or patterns that cover the declared type of the value (`match_grade/3`). -/
def covered (ctx : List Slot) (e : Expr) (rows : List (List Pat)) : Bool :=
  rows.any (fun r => r.length == 1 && r.all Pat.isVar) || (valueType P ctx e).any fun T => cover rows [T]

mutual
def infer (ctx : List Slot) : Expr → Grade
  | .lit _ | .var _ | .collapse _ => .one
  | .arith _ a b => seq (infer ctx a) (infer ctx b)
  | .call f args => seq (inferSeq ctx args) (D f).grade
  | .papp _ args => inferSeq ctx args
  | .callVar i args => seq (inferSeq ctx args) ((ctx.getD i (none, none)).2.getD .any)
  | .superpose es => inferChoice ctx es
  | .space _ => .any
  | .if3 c t e => seq (infer ctx c) (join (infer ctx t) (infer ctx e))
  | .if2 c t => seq (infer ctx c) (join (infer ctx t) .zero)
  | .let_ p e b => seq (infer ctx e)
      (seq (if covered cover P ctx e [[p]] then .one else .optional) (infer ((none, none) :: ctx) b))
  | .case s bs => seq (infer ctx s)
      (if covered cover P ctx s (bs.map fun b => [b.1]) then joinAll (inferCase ((none, none) :: ctx) bs)
        else join (joinAll (inferCase ((none, none) :: ctx) bs)) .zero)
  | .once e => once (infer ctx e)
def inferSeq (ctx : List Slot) : List Expr → Grade
  | [] => .one
  | e :: es => seq (infer ctx e) (inferSeq ctx es)
def inferChoice (ctx : List Slot) : List Expr → Grade
  | [] => .zero
  | e :: es => choice (infer ctx e) (inferChoice ctx es)
def inferCase (ctx : List Slot) : List (Pat × Expr) → List Grade
  | [] => []
  | (_, e) :: bs => infer ctx e :: inferCase ctx bs
end

/-- `function_grade/5`: a committing function's clauses joined, and `zero` too unless its heads
cover its parameter types; another function's clauses added, each joined with `zero` unless its
head is all variables. -/
def Fn.grade (fn : Fn) : Grade :=
  if fn.commits then
    if cover (fn.clauses.map Clause.head) fn.types
    then joinAll (fn.clauses.map fun c => infer cover P D fn.slots c.body)
    else join (joinAll (fn.clauses.map fun c => infer cover P D fn.slots c.body)) .zero
  else (fn.clauses.map fun c =>
      if c.head.length = fn.params.length ∧ c.head.all Pat.isVar then infer cover P D fn.slots c.body
      else join (infer cover P D fn.slots c.body) .zero).foldr choice .zero

theorem refines_trans {a b c : Grade} (h₁ : Refines a b) (h₂ : Refines b c) : Refines a c :=
  fun n h => h₂ n (h₁ n h)

theorem refines_joinAll : ∀ {gs : List Grade} {g : Grade}, g ∈ gs → Refines g (joinAll gs)
  | [_], _, h => by rw [List.mem_singleton.1 h]; exact fun _ => id
  | g' :: g'' :: gs, g, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact join_left _ _
      · exact refines_trans (refines_joinAll h) (join_right _ _)

theorem mem_inferCase (ctx : List Slot) :
    ∀ {bs : List (Pat × Expr)} {b}, b ∈ bs → infer cover P D ctx b.2 ∈ inferCase cover P D ctx bs
  | (_, _) :: bs, b, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp [inferCase]
      · simp only [inferCase]; exact List.mem_cons_of_mem _ (mem_inferCase ctx h)

theorem seq_one_left (g : Grade) : seq .one g = g := by cases g <;> rfl

theorem allows_seq_optional {g : Grade} {k : Nat} (h : Allows g k) : Allows (seq .optional g) k := by
  cases g <;> simp_all [Allows, seq]

theorem allows_seq_optional_zero (g : Grade) : Allows (seq .optional g) 0 := by
  cases g <;> simp [Allows, seq]

/-! ## Evaluation -/

def truthy : Term → Bool
  | .lit (.bool true) => true
  | _ => false

/-- Run the continuation on each answer, in order; `none` stops the run. -/
def bindAll {α β : Type} (k : α → Option (List β)) : List α → Option (List β)
  | [] => some []
  | x :: xs => do let ys ← k x; let zs ← bindAll k xs; pure (ys ++ zs)

def mapAll {α β : Type} (k : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do let y ← k x; let ys ← mapAll k xs; pure (y :: ys)

/-- The argument vectors of a call: one per choice of an answer for each argument. -/
def product : List (List Term) → List (List Term)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (product xss).map (x :: ·)

variable (chk : Checker sig)

/-- The answers of `f`'s clauses: a committing function's first matching clause, another
function's every matching clause. -/
def clauseAnswers (run : List Term → Expr → Option (List Term)) (f : String) (vs : List Term) :
    Option (List Term) :=
  if (P f).commits then
    match (P f).clauses.find? (fun c => Pat.unifyRow c.head vs) with
    | some c => run vs c.body
    | none => some []
  else bindAll (fun c => if Pat.unifyRow c.head vs then run vs c.body else some []) (P f).clauses

/-- A call of `f` on argument values: a type error unless they fit the parameters, then the
clauses' answers, each of which must fit the result. -/
def callWith (run : List Term → Expr → Option (List Term)) (f : String) (vs : List Term) :
    Option (List Term) :=
  if chk.testAll vs (P f).types then
    (clauseAnswers P run f vs).bind fun as => if as.all (chk.test · (P f).res) then some as else none
  else none

def eval : Nat → List Term → Expr → Option (List Term)
  | 0, _, _ => none
  | n + 1, env, e => match e with
    | .lit t => some [t]
    | .var i => some [env.getD i (.app [])]
    | .arith op a b => do
        let xs ← eval n env a
        let ys ← eval n env b
        pure (xs.flatMap fun x => ys.map (op x))
    | .call f args => do
        let vss ← mapAll (eval n env) args
        bindAll (callWith P chk (eval n) f) (product vss)
    | .papp f args => do
        let vss ← mapAll (eval n env) args
        pure ((product vss).map fun vs => .app (.sym f :: vs))
    | .callVar i args => match (env.getD i (.app [])).closure? with
      | some (g, bs) => do
          let vss ← mapAll (eval n env) args
          bindAll (fun vs => callWith P chk (eval n) g (bs ++ vs)) (product vss)
      | none => none
    | .superpose es => do
        let ass ← mapAll (eval n env) es
        pure ass.flatten
    | .space q => some (q env)
    | .if3 c t e => do
        let cs ← eval n env c
        bindAll (fun v => if truthy v then eval n env t else eval n env e) cs
    | .if2 c t => do
        let cs ← eval n env c
        bindAll (fun v => if truthy v then eval n env t else some []) cs
    | .let_ p e b => do
        let xs ← eval n env e
        bindAll (fun x => if p.unify x then eval n (x :: env) b else some []) xs
    | .case s bs => do
        let ss ← eval n env s
        bindAll (fun v => match bs.find? (fun b => b.1.unify v) with
          | some b => eval n (v :: env) b.2
          | none => some []) ss
    | .once e => do let xs ← eval n env e; pure (xs.take 1)
    | .collapse e => do let xs ← eval n env e; pure [.app xs]

/-- A call with fuel `n`. -/
def call (n : Nat) (f : String) (vs : List Term) : Option (List Term) :=
  callWith P chk (eval P chk n) f vs

/-! ## Soundness -/

theorem bindAll_some {α β : Type} {k : α → Option (List β)} :
    ∀ {xs : List α} {ys : List β}, bindAll k xs = some ys →
      ∃ yss, List.Forall₂ (fun x zs => k x = some zs) xs yss ∧ ys = yss.flatten
  | [], ys, h => ⟨[], .nil, by simp [bindAll] at h; simp [h]⟩
  | x :: xs, ys, h => by
      simp only [bindAll, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨y, hy, zs, hzs, rfl⟩ := h
      obtain ⟨yss, hf, rfl⟩ := bindAll_some hzs
      exact ⟨y :: yss, .cons hy hf, rfl⟩

theorem mapAll_some {α β : Type} {k : α → Option β} :
    ∀ {xs : List α} {ys : List β}, mapAll k xs = some ys → List.Forall₂ (fun x y => k x = some y) xs ys
  | [], ys, h => by simp [mapAll] at h; subst h; exact .nil
  | x :: xs, ys, h => by
      simp only [mapAll, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨y, hy, zs, hzs, rfl⟩ := h
      exact .cons hy (mapAll_some hzs)

theorem forall₂_imp_right {α β : Type} {R : α → β → Prop} {p : β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → (∀ x ∈ xs, ∀ y, R x y → p y) →
      ∀ y ∈ ys, p y
  | _, _, .nil, _ => by simp
  | _, _, .cons hxy hr, h => by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h _ (by simp) _ hxy
      · exact forall₂_imp_right hr (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Binding a graded producer to a graded continuation. -/
theorem bindAll_sound {α β : Type} {k : α → Option (List β)} {xs : List α} {ys : List β}
    {a b : Grade} (h : bindAll k xs = some ys) (ha : Allows a xs.length)
    (hk : ∀ x ∈ xs, ∀ zs, k x = some zs → Allows b zs.length) : Allows (seq a b) ys.length := by
  obtain ⟨yss, hf, rfl⟩ := bindAll_some h
  have := bind_sound a b yss id (hf.length_eq ▸ ha) (forall₂_imp_right hf hk)
  simpa using this

theorem product_sound {ctx : List Slot} :
    ∀ {es : List Expr} {vss : List (List Term)},
      List.Forall₂ (fun e vs => Allows (infer cover P D ctx e) vs.length) es vss →
        Allows (inferSeq cover P D ctx es) (product vss).length
  | _, _, .nil => rfl
  | _, _, .cons (b := vs) (l₂ := vss) h hr => by
      have := bind_sound _ _ vs (fun x => (product vss).map (x :: ·)) h
        (fun _ _ => by simpa using product_sound hr)
      simpa [inferSeq, product] using this

theorem inferChoice_eq (ctx : List Slot) :
    ∀ es, inferChoice cover P D ctx es = (es.map (infer cover P D ctx)).foldr choice .zero
  | [] => rfl
  | e :: es => by simp [inferChoice, inferChoice_eq ctx es]

theorem foldr_choice_sound :
    ∀ {gs : List Grade} {yss : List (List Term)},
      List.Forall₂ (fun g (ys : List Term) => Allows g ys.length) gs yss →
        Allows (gs.foldr choice .zero) yss.flatten.length
  | _, _, .nil => rfl
  | _, _, .cons h hr => by simpa using append_sound _ _ _ _ h (foldr_choice_sound hr)

theorem unifyRow_vars : ∀ {ps : List Pat} {vs : List Term}, ps.all Pat.isVar = true →
    ps.length = vs.length → Pat.unifyRow ps vs = true
  | [], [], _, _ => rfl
  | .var :: ps, v :: vs, h, hl => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [Pat.unifyRow, Pat.var_unify, unifyRow_vars h.2 (by simpa using hl)]

/-- Every function's grade validates against its declaration (assumed for callees). -/
def Validated : Prop := ∀ f, validates ((P f).grade cover P D) (D f) = true

/-- A closure passed for a parameter declared with an arrow of determinism `d` is a function
whose declaration refines `d`. The contract checks only the closure's arity, so this is assumed
(a lambda is a function whose grade is its body's). -/
def ClosuresRespect : Prop :=
  ∀ f vs, chk.testAll vs (P f).types = true → ∀ i d g bs,
    ((P f).params.getD i (.unknown, none)).2 = some d →
    (vs.getD i (.app [])).closure? = some (g, bs) → Refines (D g).grade d.grade

variable (sig) in
/-- The environment honours what the analysis knows of it. -/
def EnvOK (ctx : List Slot) (env : List Term) : Prop :=
  ∀ i, (∀ T, (ctx.getD i (none, none)).1 = some T → Fits sig (env.getD i (.app [])) T) ∧
    ∀ d, (ctx.getD i (none, none)).2 = some d →
      ∀ g bs, (env.getD i (.app [])).closure? = some (g, bs) → Refines (D g).grade d

theorem EnvOK.push {ctx : List Slot} {env : List Term} (h : EnvOK sig D ctx env) (x : Term) :
    EnvOK sig D ((none, none) :: ctx) (x :: env) := by
  intro i
  cases i with
  | zero => simp
  | succ i => simpa using h i

theorem envOK_slots (hcl : ClosuresRespect P D chk) {f : String} {vs : List Term}
    (ht : chk.testAll vs (P f).types = true) : EnvOK sig D (P f).slots vs := by
  have hfit := (fitsAll_iff sig _ _).1 ((chk.testAll_iff _ _).1 ht)
  intro i
  by_cases hi : i < (P f).params.length
  · have hv : i < vs.length := by simpa [hfit.1, Fn.types] using hi
    simp only [Fn.slots, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
      List.getElem?_eq_getElem hv]
    refine ⟨fun T hT => ?_, fun d hd g bs hg => ?_⟩
    · cases hT
      simpa [Fn.types] using hfit.2 i hv (by simpa [Fn.types] using hi)
    · obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.1 hd
      exact hcl f vs ht i d' g bs (by simp [List.getD_eq_getElem?_getD, hi, hd'])
        (by simpa [List.getD_eq_getElem?_getD, hv] using hg)
  · simp [Fn.slots, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

theorem callWith_sound (hv : Validated cover P D) (hc : CoverSound sig cover)
    (hcl : ClosuresRespect P D chk) {run : List Term → Expr → Option (List Term)}
    (hrun : ∀ ctx env e as, EnvOK sig D ctx env → run env e = some as →
      Allows (infer cover P D ctx e) as.length)
    {f : String} {vs as : List Term} (h : callWith P chk run f vs = some as) :
    Allows (D f).grade as.length ∧ ∀ x ∈ as, Fits sig x (P f).res := by
  have hval := (validates_iff _ _).1 (hv f)
  unfold callWith at h
  split at h
  · next ht =>
      have he := envOK_slots P D chk hcl ht
      have hfit := (chk.testAll_iff _ _).1 ht
      obtain ⟨as', hinner, hres⟩ := Option.bind_eq_some_iff.1 h
      split at hres
      · next hall =>
          cases hres
          refine ⟨hval _ ?_, fun x hx => (chk.test_iff _ _).1 (List.all_eq_true.1 hall x hx)⟩
          unfold Fn.grade
          unfold clauseAnswers at hinner
          split at hinner
          · next hcommit =>
              simp only [hcommit, if_true]
              split at hinner
              · next c hc' =>
                  have hmem := List.mem_map_of_mem (f := fun c => infer cover P D (P f).slots c.body)
                    (List.mem_of_find?_eq_some hc')
                  have hg := hrun _ _ _ _ he hinner
                  split
                  · exact refines_joinAll hmem _ hg
                  · exact refines_trans (refines_joinAll hmem) (join_left _ _) _ hg
              · next hnone =>
                  cases hinner
                  split
                  · next hcov =>
                      obtain ⟨row, hrow, hm⟩ := hc _ _ hcov _ hfit
                      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hrow
                      exact absurd hm (by simpa using List.find?_eq_none.1 hnone c hc')
                  · exact join_right _ _ 0 rfl
          · next hcommit =>
              simp only [hcommit, Bool.false_eq_true, if_false]
              obtain ⟨yss, hf, rfl⟩ := bindAll_some hinner
              refine foldr_choice_sound (List.forall₂_map_left_iff.2 (hf.imp fun c ys hk => ?_))
              split at hk
              · next hu =>
                  have hg := hrun _ _ _ _ he hk
                  split
                  · exact hg
                  · exact join_left _ _ _ hg
              · cases hk
                split
                · next hvar =>
                    have hl : c.head.length = vs.length := by
                      rw [hvar.1, hfit.length_eq]; simp [Fn.types]
                    exact absurd (unifyRow_vars hvar.2 hl) ‹_›
                · exact join_right _ _ 0 rfl
      · cases hres
  · cases h

/-- Every completed evaluation is allowed by its inferred grade, and its values fit their
declared type. -/
theorem eval_sound (hv : Validated cover P D) (hc : CoverSound sig cover)
    (hcl : ClosuresRespect P D chk) :
    ∀ n ctx env e as, EnvOK sig D ctx env → eval P chk n env e = some as →
      Allows (infer cover P D ctx e) as.length ∧
        ∀ T, valueType P ctx e = some T → ∀ x ∈ as, Fits sig x T := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; cases h
  | succ n ih =>
    have hcall : ∀ {f vs as}, callWith P chk (eval P chk n) f vs = some as →
        Allows (D f).grade as.length ∧ ∀ x ∈ as, Fits sig x (P f).res :=
      fun h => callWith_sound cover P D chk hv hc hcl (fun _ _ _ _ he h => (ih _ _ _ _ he h).1) h
    have hcov : ∀ {ctx env} {e : Expr} {rows : List (List Pat)} {xs : List Term},
        EnvOK sig D ctx env → eval P chk n env e = some xs → covered cover P ctx e rows = true →
          ∀ x ∈ xs, ∃ row ∈ rows, Pat.unifyRow row [x] = true := by
      intro ctx env e rows xs he hx hcv x hmem
      rcases Bool.or_eq_true_iff.1 hcv with hv | hcv
      · obtain ⟨r, hr, hrv⟩ := List.any_eq_true.1 hv
        simp only [Bool.and_eq_true, beq_iff_eq] at hrv
        exact ⟨r, hr, unifyRow_vars hrv.2 (by simp [hrv.1])⟩
      obtain ⟨T, hT, hTc⟩ := (Option.any_eq_true _ _).1 hcv
      exact hc _ _ hTc _ (.cons ((ih _ _ _ _ he hx).2 T hT x hmem) .nil)
    intro ctx env e as he h
    have hseq : ∀ {args vss}, mapAll (eval P chk n env) args = some vss →
        Allows (inferSeq cover P D ctx args) (product vss).length := fun hvss =>
      product_sound cover P D ((mapAll_some hvss).imp fun e vs hv => (ih _ _ _ _ he hv).1)
    cases e <;> simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    next t => subst h; exact ⟨rfl, by simp [valueType]⟩
    next i =>
      subst h
      refine ⟨rfl, fun T hT x hx => ?_⟩
      simp only [List.mem_singleton] at hx; subst hx
      exact (he i).1 T hT
    next op a b =>
      obtain ⟨xs, hxs, ys, hys, rfl⟩ := h
      exact ⟨bind_sound _ _ xs _ (ih _ _ _ _ he hxs).1 fun _ _ => by
        simpa using (ih _ _ _ _ he hys).1, by simp [valueType]⟩
    next f args =>
      obtain ⟨vss, hvss, h⟩ := h
      refine ⟨bindAll_sound h (hseq hvss) fun vs _ zs hz => (hcall hz).1, fun T hT x hx => ?_⟩
      simp only [valueType, Option.some.injEq] at hT; subst hT
      obtain ⟨yss, hf, rfl⟩ := bindAll_some h
      obtain ⟨zs, hzs, hxz⟩ := List.mem_flatten.1 hx
      exact forall₂_imp_right (p := fun zs => ∀ x ∈ zs, Fits sig x (P f).res) hf
        (fun _ _ _ hz => (hcall hz).2) zs hzs x hxz
    next f args =>
      obtain ⟨vss, hvss, rfl⟩ := h
      exact ⟨by simpa [infer] using hseq hvss, by simp [valueType]⟩
    next i args =>
      split at h
      · next g bs hg =>
          obtain ⟨vss, hvss, h⟩ := Option.bind_eq_some_iff.1 h
          refine ⟨bindAll_sound h (hseq hvss) fun vs _ zs hz => ?_, by simp [valueType]⟩
          have hz := (hcall hz).1
          cases hs : (ctx.getD i (none, none)).2 with
          | none => trivial
          | some d => exact (he i).2 d hs g bs hg _ hz
      · cases h
    next es =>
      obtain ⟨ass, hass, rfl⟩ := h
      refine ⟨?_, by simp [valueType]⟩
      simpa [infer, inferChoice_eq] using foldr_choice_sound (List.forall₂_map_left_iff.2
        ((mapAll_some hass).imp fun e as ha => (ih _ _ _ _ he ha).1))
    next q => exact ⟨trivial, by simp [valueType]⟩
    next c t e =>
      obtain ⟨cs, hcs, h⟩ := h
      refine ⟨bindAll_sound h (ih _ _ _ _ he hcs).1 fun v _ zs hz => ?_, by simp [valueType]⟩
      split at hz
      · exact join_left _ _ _ (ih _ _ _ _ he hz).1
      · exact join_right _ _ _ (ih _ _ _ _ he hz).1
    next c t =>
      obtain ⟨cs, hcs, h⟩ := h
      refine ⟨bindAll_sound h (ih _ _ _ _ he hcs).1 fun v _ zs hz => ?_, by simp [valueType]⟩
      split at hz
      · exact join_left _ _ _ (ih _ _ _ _ he hz).1
      · cases hz; exact join_right _ _ _ rfl
    next p e b =>
      obtain ⟨xs, hxs, h⟩ := h
      refine ⟨bindAll_sound h (ih _ _ _ _ he hxs).1 fun x hx zs hz => ?_, by simp [valueType]⟩
      split at hz
      · have hb := (ih _ _ _ _ (he.push D x) hz).1
        split
        · rw [seq_one_left]; exact hb
        · exact allows_seq_optional hb
      · cases hz
        split
        · next hcv =>
            obtain ⟨row, hrow, hm⟩ := hcov he hxs hcv x hx
            simp only [List.mem_singleton] at hrow; subst hrow
            simp_all [Pat.unifyRow]
        · exact allows_seq_optional_zero _
    next s bs =>
      obtain ⟨ss, hss, h⟩ := h
      refine ⟨bindAll_sound h (ih _ _ _ _ he hss).1 fun v hv zs hz => ?_, by simp [valueType]⟩
      split at hz
      · next b hb =>
          have hg := (ih _ _ _ _ (he.push D v) hz).1
          have hmem := mem_inferCase cover P D ((none, none) :: ctx) (List.mem_of_find?_eq_some hb)
          split
          · exact refines_joinAll hmem _ hg
          · exact refines_trans (refines_joinAll hmem) (join_left _ _) _ hg
      · next hnone =>
          cases hz
          split
          · next hcv =>
              obtain ⟨row, hrow, hm⟩ := hcov he hss hcv v hv
              obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hrow
              exact absurd (by simpa [Pat.unifyRow] using hm) (List.find?_eq_none.1 hnone b hb)
          · exact join_right _ _ 0 rfl
    next e =>
      obtain ⟨xs, hxs, rfl⟩ := h
      exact ⟨take_one_sound _ xs (ih _ _ _ _ he hxs).1, by simp [valueType]⟩
    next e => obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, by simp [valueType]⟩

/-- `det_validation_sound`: if every function validates against its declaration, every answer
list of a call to `f` is allowed by `f`'s declaration. -/
theorem det_validation_sound (hv : Validated cover P D) (hc : CoverSound sig cover)
    (hcl : ClosuresRespect P D chk) (n : Nat) (f : String) (vs as : List Term)
    (h : call P chk n f vs = some as) : Allows (D f).grade as.length :=
  (callWith_sound cover P D chk hv hc hcl (fun _ _ _ _ he h => (eval_sound cover P D chk hv hc hcl n _ _ _ _ he h).1) h).1

/-! ## Examples -/

namespace Examples

def sig₀ : Sig := ⟨[], [], [], fun _ => none⟩

def two : Expr := .superpose [.lit (.sym "a"), .lit (.sym "b")]

/-- `(= (f) Body)`, committing, without parameters. -/
def prog (body : Expr) : String → Fn := fun _ => ⟨[], .unknown, [⟨[], body⟩], true⟩

/-- A `superpose` of two literals is refuted as `det`, and rightly: the call has two answers. -/
theorem superpose_refuted_as_det (chk : Checker sig₀) :
    validates ((prog two "f").grade (coverN sig₀ 1) (prog two) fun _ => .det) .det = false ∧
      call (prog two) chk 2 "f" [] = some [.sym "a", .sym "b"] ∧
      ¬ Allows Declaration.det.grade 2 := by
  refine ⟨CheckedCardinality.Controls.duplicate_values_are_not_det, ?_, by decide⟩
  have ht : ∀ v, chk.test v .unknown = true := fun v => (chk.test_iff _ _).2 (.unknown v)
  simp [call, callWith, clauseAnswers, prog, two, eval, mapAll, Fn.types, Checker.testAll,
    Pat.unifyRow, ht]

/-- `not` on `Bool`, with a clause for each of the given heads. -/
def notB (heads : List Bool) : String → Fn := fun _ =>
  ⟨[(.prim .bool, none)], .prim .bool,
    heads.map fun b => ⟨[.lit (.bool b)], .lit (.lit (.bool !b))⟩, true⟩

/-- Heads `True` and `False` cover `Bool`: the function is `det`. With `True` alone it is
`semidet`, not `det`. -/
theorem covering_heads :
    validates ((notB [true, false] "not").grade (coverN sig₀ 3) (notB [true, false])
      fun _ => .det) .det = true ∧
    validates ((notB [true] "not").grade (coverN sig₀ 3) (notB [true]) fun _ => .det) .det = false ∧
    validates ((notB [true] "not").grade (coverN sig₀ 3) (notB [true]) fun _ => .semidet)
      .semidet = true := by decide

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping
