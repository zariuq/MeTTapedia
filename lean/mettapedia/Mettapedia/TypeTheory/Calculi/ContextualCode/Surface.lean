import Mathlib.Logic.Equiv.Basic
import Mettapedia.TypeTheory.Calculi.ContextualCode.Confluence

/-!
# Reading Prime's surface syntax

`Surface` is the syntax as Prime writes it, with names. `resolve` reads it in
a context of bound names: a bound name becomes a variable, any other name a
symbol, so unknown names stay data.

* `lam` and `let` bind names; `(let x V B)` is read as `((lam x B) V)`.
* `(quote M ($x₁ … $x_k))`, with the list last, is read in the context of its
  own parameters only: a quotation is closed in every outer name, `$`-names
  included. `(quote M)` is the case of the empty list.
* The literal `*@M` reads `M` in place; this is how the draft refers to the
  value bound to a binder key.
* The bracket `T[A]` is read as the derived form `inst`, which goes through
  `lift`.

`resolve_perm` states that reading commutes with renaming names, and
`alpha_quote` derives from it that renaming a quotation's parameters does not
change the quotation. The examples reproduce lines of the draft's fixture
`lambda_names.metta` and show where the calculus and the draft part ways.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-- Prime's surface syntax. `quote M k xs` is `(quote M (xs 0 … xs (k-1)))`. -/
inductive Surface : Type where
  | atom : String → Surface
  | lam : String → Surface → Surface
  | app : Surface → Surface → Surface
  | quote : Surface → (k : Nat) → (Fin k → String) → Surface
  | lift : Surface → Surface
  | drop : Surface → Surface
  | letIn : String → Surface → Surface → Surface
  | bracket : Surface → Surface → Surface

namespace Surface

/-- The innermost binding of a name. -/
def lookup : {n : Nat} → (Fin n → String) → String → Option (Fin n)
  | 0, _, _ => none
  | _ + 1, Γ, s => if Γ 0 = s then some 0 else (lookup (fun i => Γ i.succ) s).map Fin.succ

/-- Read a surface term in a context of bound names. -/
def resolve : {n : Nat} → (Fin n → String) → Surface → Term n
  | _, Γ, .atom s =>
      match lookup Γ s with
      | some i => .var i
      | none => .sym s
  | _, Γ, .lam x M => .lam (resolve (Fin.cases x Γ) M)
  | _, Γ, .app f a => .app (resolve Γ f) (resolve Γ a)
  | _, _, .quote M k xs => .cquote k (resolve (fun i => xs i.rev) M)
  | _, Γ, .lift M => .lift (resolve Γ M)
  | _, Γ, .drop (.quote M 0 _) => resolve Γ M
  | _, Γ, .drop K => .drop (resolve Γ K)
  | _, Γ, .letIn x V B => .app (.lam (resolve (Fin.cases x Γ) B)) (resolve Γ V)
  | _, Γ, .bracket T A => inst (resolve Γ T) (resolve Γ A)

/-- Rename every name. -/
def perm (π : String → String) : Surface → Surface
  | .atom s => .atom (π s)
  | .lam x M => .lam (π x) (perm π M)
  | .app f a => .app (perm π f) (perm π a)
  | .quote M k xs => .quote (perm π M) k (fun i => π (xs i))
  | .lift M => .lift (perm π M)
  | .drop K => .drop (perm π K)
  | .letIn x V B => .letIn (π x) (perm π V) (perm π B)
  | .bracket T A => .bracket (perm π T) (perm π A)

end Surface

/-! ## Renaming symbols -/

/-- Rename the symbols of a pattern. -/
def Pat.renameSyms (π : String → String) {m : Nat} : {k : Nat} → Pat m k → Pat m k
  | _, .hole j => .hole j
  | _, .var i => .var i
  | _, .sym s => .sym (π s)
  | _, .lam P => .lam (renameSyms π P)
  | _, .app P Q => .app (renameSyms π P) (renameSyms π Q)
  | _, .cquote j P => .cquote j (renameSyms π P)
  | _, .lift P => .lift (renameSyms π P)
  | _, .drop P => .drop (renameSyms π P)

/-- Rename the symbols of a term, inside templates too. -/
def Term.renameSyms (π : String → String) : {n : Nat} → Term n → Term n
  | _, .var i => .var i
  | _, .sym s => .sym (π s)
  | _, .lam b => .lam (renameSyms π b)
  | _, .app f a => .app (renameSyms π f) (renameSyms π a)
  | _, .cquote k M => .cquote k (renameSyms π M)
  | _, .lift M => .lift (renameSyms π M)
  | _, .drop K => .drop (renameSyms π K)
  | _, .cmatch k K P F => .cmatch k (renameSyms π K) (P.renameSyms π) (renameSyms π F)

/-- The symbol `s` occurs in a pattern. -/
def Pat.SymIn (s : String) {m : Nat} : {k : Nat} → Pat m k → Prop
  | _, .hole _ => False
  | _, .var _ => False
  | _, .sym t => t = s
  | _, .lam P => SymIn s P
  | _, .app P Q => SymIn s P ∨ SymIn s Q
  | _, .cquote _ P => SymIn s P
  | _, .lift P => SymIn s P
  | _, .drop P => SymIn s P

/-- The symbol `s` occurs in a term, inside templates too. -/
def Term.SymIn (s : String) : {n : Nat} → Term n → Prop
  | _, .var _ => False
  | _, .sym t => t = s
  | _, .lam b => SymIn s b
  | _, .app f a => SymIn s f ∨ SymIn s a
  | _, .cquote _ M => SymIn s M
  | _, .lift M => SymIn s M
  | _, .drop K => SymIn s K
  | _, .cmatch _ K P F => SymIn s K ∨ P.SymIn s ∨ SymIn s F

theorem Pat.renameSyms_eq_self (π : String → String) {m : Nat} :
    ∀ {k : Nat} (P : Pat m k), (∀ s, P.SymIn s → π s = s) → P.renameSyms π = P
  | _, .hole _, _ => rfl
  | _, .var _, _ => rfl
  | _, .sym t, h => by simp only [renameSyms, h t rfl]
  | _, .lam P, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π P h]
  | _, .app P Q, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π P (fun s hs => h s (.inl hs)),
        renameSyms_eq_self π Q (fun s hs => h s (.inr hs))]
  | _, .cquote _ P, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π P h]
  | _, .lift P, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π P h]
  | _, .drop P, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π P h]

/-- Renaming symbols that a term does not contain changes nothing. -/
theorem Term.renameSyms_eq_self (π : String → String) :
    ∀ {n : Nat} (M : Term n), (∀ s, M.SymIn s → π s = s) → M.renameSyms π = M
  | _, .var _, _ => rfl
  | _, .sym t, h => by simp only [renameSyms, h t rfl]
  | _, .lam b, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π b h]
  | _, .app f a, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π f (fun s hs => h s (.inl hs)),
        renameSyms_eq_self π a (fun s hs => h s (.inr hs))]
  | _, .cquote _ M, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π M h]
  | _, .lift M, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π M h]
  | _, .drop K, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π K h]
  | _, .cmatch _ K P F, h => by
      simp only [renameSyms]
      rw [renameSyms_eq_self π K (fun s hs => h s (.inl hs)),
        Pat.renameSyms_eq_self π P (fun s hs => h s (.inr (.inl hs))),
        renameSyms_eq_self π F (fun s hs => h s (.inr (.inr hs)))]

namespace Surface

/-! ## Reading commutes with renaming names -/

theorem lookup_perm {π : String → String} (hπ : Function.Injective π) :
    ∀ {n : Nat} (Γ : Fin n → String) (s : String),
      lookup (fun i => π (Γ i)) (π s) = lookup Γ s
  | 0, _, _ => rfl
  | _ + 1, Γ, s => by
      simp only [lookup, hπ.eq_iff]
      rw [lookup_perm hπ (fun i => Γ i.succ) s]

theorem cases_perm {n : Nat} (π : String → String) (x : String) (Γ : Fin n → String) :
    (Fin.cases (π x) (fun i => π (Γ i)) : Fin (n + 1) → String) =
      fun i => π (Fin.cases x Γ i) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- **Reading commutes with renaming names**, for every injective renaming:
the variables are the same, and the symbols are renamed. -/
theorem resolve_perm {π : String → String} (hπ : Function.Injective π) :
    ∀ (M : Surface) {n : Nat} (Γ : Fin n → String),
      resolve (fun i => π (Γ i)) (M.perm π) = (resolve Γ M).renameSyms π
  | .atom s, _, Γ => by
      simp only [perm, resolve, lookup_perm hπ]
      cases lookup Γ s <;> rfl
  | .lam x M, _, Γ => by
      simp only [perm, resolve, Term.renameSyms]
      rw [cases_perm, resolve_perm hπ M]
  | .app f a, _, Γ => by
      simp only [perm, resolve, Term.renameSyms]
      rw [resolve_perm hπ f, resolve_perm hπ a]
  | .quote M k xs, _, _ => by
      simp only [perm, resolve, Term.renameSyms]
      rw [resolve_perm hπ M (fun i => xs i.rev)]
  | .lift M, _, Γ => by
      simp only [perm, resolve, Term.renameSyms]
      rw [resolve_perm hπ M]
  | .drop K, _, Γ => by
      cases K with
      | quote M k xs =>
          cases k with
          | zero =>
              simp only [perm, resolve]
              exact resolve_perm hπ M Γ
          | succ k =>
              simp only [perm, resolve, Term.renameSyms]
              rw [resolve_perm hπ M (fun i => xs i.rev)]
      | atom s =>
          have := resolve_perm hπ (.atom s) Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
      | lam x M =>
          have := resolve_perm hπ (.lam x M) Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
      | app f a =>
          have := resolve_perm hπ (.app f a) Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
      | lift M =>
          have := resolve_perm hπ (.lift M) Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
      | drop K' =>
          have := resolve_perm hπ (.drop K') Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
      | letIn x V B =>
          have := resolve_perm hπ (.letIn x V B) Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
      | bracket T A =>
          have := resolve_perm hπ (.bracket T A) Γ
          simp only [perm, resolve, Term.renameSyms] at this ⊢
          rw [this]
  | .letIn x V B, _, Γ => by
      simp only [perm, resolve, Term.renameSyms]
      rw [cases_perm, resolve_perm hπ B, resolve_perm hπ V]
  | .bracket T A, _, Γ => by
      simp only [perm, resolve, inst, Term.renameSyms]
      rw [resolve_perm hπ T, resolve_perm hπ A]

/-- **α-equivalence by construction.** Renaming the names of a quotation,
its parameters included, by an injective renaming that fixes the symbols the
quotation contains, gives the same template. -/
theorem alpha_quote {π : String → String} (hπ : Function.Injective π) (M : Surface) (k : Nat)
    (xs : Fin k → String)
    (fixes : ∀ s, (resolve (fun i => xs i.rev) M).SymIn s → π s = s)
    {n : Nat} (Γ : Fin n → String) :
    resolve Γ (.quote (M.perm π) k (fun i => π (xs i))) = resolve Γ (.quote M k xs) := by
  simp only [resolve]
  rw [resolve_perm hπ M (fun i => xs i.rev), Term.renameSyms_eq_self π _ fixes]

end Surface

/-! ## Examples -/

open Surface

/-- No parameters: `@M` is `(quote M ())`. -/
def noParams : Fin 0 → String := fun i => i.elim0

/-- `@M`. -/
def at_ (M : Surface) : Surface := .quote M 0 noParams

/-- The empty context. -/
def top : Fin 0 → String := fun i => i.elim0

/-- `(quote (f $x) ($x))` and `(quote (f $y) ($y))` are the same template. -/
theorem alpha_example :
    resolve top (.quote (.app (.atom "f") (.atom "$x")) 1 (fun _ => "$x")) =
      resolve top (.quote (.app (.atom "f") (.atom "$y")) 1 (fun _ => "$y")) := rfl

/-- The same equation as an instance of `alpha_quote`: swap `$x` and `$y`. -/
theorem alpha_example_by_swap :
    resolve top (.quote (.app (.atom "f") (.atom "$x")) 1 (fun _ => "$x")) =
      resolve top (.quote (.app (.atom "f") (.atom "$y")) 1 (fun _ => "$y")) := by
  have body : resolve (fun i : Fin 1 => (fun _ => "$x") i.rev) (.app (.atom "f") (.atom "$x")) =
      .app (.sym "f") (.var 0) := rfl
  have swapped := alpha_quote (Equiv.swap "$x" "$y").injective (.app (.atom "f") (.atom "$x")) 1
    (fun _ => "$x") (by
      intro s hs
      rw [body] at hs
      simp only [Term.SymIn, or_false] at hs
      subst hs
      rfl) top
  exact swapped.symm

/-- `((lam x @x) a)` gives `@x`: a quotation keeps the binder's name. -/
theorem lambda_names_quote :
    Steps (resolve top (.app (.lam "x" (at_ (.atom "x"))) (.atom "a")))
      (.cquote 0 (.sym "x")) :=
  .single (.beta _ _)

/-- `((lam x *@x) payload)` gives `payload`: `*@x` refers to the binder. -/
theorem lambda_names_reference :
    Steps (resolve top (.app (.lam "x" (.drop (at_ (.atom "x")))) (.atom "payload")))
      (.sym "payload") :=
  .single (.beta _ _)

/-- `((lam x *@*@x) payload)` gives `payload`. -/
theorem lambda_names_double_reference :
    Steps (resolve top (.app (.lam "x" (.drop (at_ (.drop (at_ (.atom "x")))))) (.atom "payload")))
      (.sym "payload") :=
  .single (.beta _ _)

/-- `((lam x (pair x @x)) ((lam y y) payload))` gives `(pair payload @x)`. -/
theorem lambda_names_pair :
    Steps (resolve top (.app (.lam "x" (.app (.app (.atom "pair") (.atom "x")) (at_ (.atom "x"))))
        (.app (.lam "y" (.atom "y")) (.atom "payload"))))
      (.app (.app (.sym "pair") (.sym "payload")) (.cquote 0 (.sym "x"))) :=
  (Relation.ReflTransGen.single (.appR (.beta _ _))).tail (.beta _ _)

/-- `(((lam a (lam x (pair *@a @x))) @x) inner)` gives `(pair @x @x)`: a name
passed as an argument stays literal under a binder of the same key. -/
theorem lambda_names_passed_name :
    Steps (resolve top (.app (.app (.lam "a" (.lam "x"
        (.app (.app (.atom "pair") (.drop (at_ (.atom "a")))) (at_ (.atom "x")))))
        (at_ (.atom "x"))) (.atom "inner")))
      (.app (.app (.sym "pair") (.cquote 0 (.sym "x"))) (.cquote 0 (.sym "x"))) :=
  (Relation.ReflTransGen.single (.appL (.beta _ _))).tail (.beta _ _)

/-- `((lam $x @$x) 5)` gives `(quote $x)`, as in the draft. -/
theorem lam_dollar_quote :
    Steps (resolve top (.app (.lam "$x" (at_ (.atom "$x"))) (.atom "5")))
      (.cquote 0 (.sym "$x")) :=
  .single (.beta _ _)

/-- **`(let $x 5 @$x)` gives `(quote $x)`.** `let` is β, and a quotation is
closed in `$`-names too. The draft gives `(quote 5)`. -/
theorem let_dollar_quote :
    Steps (resolve top (.letIn "$x" (.atom "5") (at_ (.atom "$x"))))
      (.cquote 0 (.sym "$x")) :=
  .single (.beta _ _)

theorem let_dollar_quote_not_five :
    ¬ Steps (resolve top (.letIn "$x" (.atom "5") (at_ (.atom "$x")))) (.cquote 0 (.sym "5")) := by
  intro h
  have := name_unique h let_dollar_quote
  exact absurd this (by decide)

/-- `(((lam k (lam x *k)) @x) payload)`. -/
def hygieneProgram : Surface :=
  .app (.app (.lam "k" (.lam "x" (.drop (.atom "k")))) (at_ (.atom "x"))) (.atom "payload")

/-- **A name passed to a binder of the same key is not captured.** The program
runs the code of the name `@x`, which is the symbol `x`. The draft gives
`payload`: the substituted `*@x` is read as a reference to the inner binder. -/
theorem hygiene_example : Steps (resolve top hygieneProgram) (.sym "x") :=
  (((Relation.ReflTransGen.single (.appL (.beta _ _))).tail (.beta _ _)).tail (.run 0 _))

theorem hygiene_not_captured : ¬ Steps (resolve top hygieneProgram) (.sym "payload") := by
  intro h
  have := normal_form_unique h hygiene_example (Normal.sym _).no_step (Normal.sym _).no_step
  exact absurd this (by decide)

/-- **The bracket**: `(quote (f $x) ($x))[@a]` gives `@(f a)`. -/
theorem bracket_example :
    Steps (resolve top (.bracket (.quote (.app (.atom "f") (.atom "$x")) 1 (fun _ => "$x"))
        (at_ (.atom "a"))))
      (.cquote 0 (.app (.sym "f") (.sym "a"))) :=
  instAll_asWritten (n := 0) (.app (.sym "f") (.var 0)) (fun _ : Fin 1 => .sym "a")
    (.app (.sym _) (.sym _) (fun _ h => by cases h))

/-- `(quote (pair $x $y) ($x $y))`: the first name written is the first
parameter filled. -/
def pairTemplate : Surface :=
  .quote (.app (.app (.atom "pair") (.atom "$x")) (.atom "$y")) 2
    (fun i : Fin 2 => if i = 0 then "$x" else "$y")

/-- Filling both parameters at once gives `@(pair a b)`. -/
theorem pair_bracket_all :
    Steps (instAll (resolve top pairTemplate)
        (fun i : Fin 2 => .cquote 0 (if i = 0 then .sym "a" else .sym "b")))
      (.cquote 0 (.app (.app (.sym "pair") (.sym "a")) (.sym "b"))) := by
  have filled : (Term.subst (fillSub (fun i : Fin 2 => if i = 0 then .sym "a" else .sym "b"))
      (.app (.app (.sym "pair") (.var 1)) (.var 0)) : Term 0) =
      .app (.app (.sym "pair") (.sym "a")) (.sym "b") := by decide
  have normal : Normal (.app (.app (.sym "pair") (.sym "a")) (.sym "b") : Term 0) :=
    .app (.app (.sym _) (.sym _) (fun _ h => by cases h)) (.sym _) (fun _ h => by cases h)
  have := instAll_asWritten (n := 0) (.app (.app (.sym "pair") (.var 1)) (.var 0))
    (fun i : Fin 2 => if i = 0 then .sym "a" else .sym "b") (filled ▸ normal)
  rw [filled] at this
  exact this

/-- Filling one parameter at a time gives the same name: running the first
bracket's `lift` releases its code, which is the simultaneous bracket. -/
theorem pair_bracket_twice :
    Steps (resolve top (.bracket (.bracket pairTemplate (at_ (.atom "a"))) (at_ (.atom "b"))))
      (.cquote 0 (.app (.app (.sym "pair") (.sym "a")) (.sym "b"))) :=
  Relation.ReflTransGen.head (.lift (.appL (.runLift _))) pair_bracket_all

end Mettapedia.TypeTheory.Calculi.ContextualCode
