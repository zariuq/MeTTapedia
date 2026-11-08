import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedShare

/-!
# Call by need and call by value agree on terminating, effect-free programs

**Call by value** (`VEval`): `bind ℓ a b` evaluates the thunk `a` first and stores its value.

**The agreement** (`need_value_agree`): for a determinate program (no data matches two equations,
so evaluation has no choice, the one effect of this core), and an expression whose bound thunks are
pure (no location, no binding) and terminate, the two strategies have the same answers. The proof
relates the two heaps cell by cell (`Related`): a by-need thunk is related to the by-value value it
would compute.

**Controls.**
- `need_answers_loop`, `value_diverges_loop`: with `(= l (call l))`, `bind 0 (call l) c` answers `c`
  by need, and has no answer by value. The loop's thunk does not terminate, which is exactly the
  agreement's hypothesis failing.
- `shared_thunk_once`: with `(= (g $x) (pair x x))`, in `bind 0 (call (g c)) (pair 0 0)` the thunk is
  forced by the first demand and read by the second; both strategies answer `((c c) (c c))`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed

open ProgramRows
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested (EPat NEquation)

variable {prog : Program}

/-! ## Call by value -/

variable (prog) in
/-- **Call by value**, over the same heaps: a bound thunk is evaluated before the body. -/
inductive VEval : Heap → NEx → Heap → Sx → Prop
  | val (H : Heap) (t : Sx) : VEval H (.val t) H t
  | pair {H H₁ H₂ : Heap} {a b : NEx} {v w : Sx} (left : VEval H a H₁ v) (right : VEval H₁ b H₂ w) :
      VEval H (.pair a b) H₂ (.cell v w)
  | call {H H₁ H₂ : Heap} {a : NEx} {w v : Sx} (j : Fin prog.length) (θ : ℕ → Sx)
      (argument : VEval H a H₁ w) (matched : (prog.get j).lhs.inst θ = w)
      (answer : VEval H₁ (instE θ (prog.get j).rhs) H₂ v) : VEval H (.call a) H₂ v
  | bind {H H₁ H' : Heap} {ℓ : ℕ} {a b : NEx} {va v : Sx} (thunk : VEval H a H₁ va) (fresh : H₁ ℓ = .empty)
      (body : VEval (H₁.set ℓ (.value va)) b H' v) : VEval H (.bind ℓ a b) H' v
  | read {H : Heap} {ℓ : ℕ} {v : Sx} (stored : H ℓ = .value v) : VEval H (.loc ℓ) H v

/-! ## Pure expressions -/

/-- No location and no binding. -/
inductive Pure : NEx → Prop
  | val (t : Sx) : Pure (.val t)
  | pair {a b : NEx} (left : Pure a) (right : Pure b) : Pure (.pair a b)
  | call {a : NEx} (argument : Pure a) : Pure (.call a)

theorem instE_pure (θ : ℕ → Sx) : ∀ p : EPat, Pure (instE θ p)
  | .val _ => .val _
  | .pair a b => .pair (instE_pure θ a) (instE_pure θ b)
  | .call a => .call (instE_pure θ a)

variable (prog) in
/-- Evaluation without a heap, for pure expressions. -/
inductive PEval : NEx → Sx → Prop
  | val (t : Sx) : PEval (.val t) t
  | pair {a b : NEx} {v w : Sx} (left : PEval a v) (right : PEval b w) : PEval (.pair a b) (.cell v w)
  | call {a : NEx} {w v : Sx} (j : Fin prog.length) (θ : ℕ → Sx) (argument : PEval a w)
      (matched : (prog.get j).lhs.inst θ = w) (answer : PEval (instE θ (prog.get j).rhs) v) : PEval (.call a) v

theorem need_pure {H H' : Heap} {e : NEx} {v : Sx} (eval : NEval prog H e H' v) (pure : Pure e) :
    H' = H ∧ PEval prog e v := by
  induction eval with
  | val H t => exact ⟨rfl, .val t⟩
  | pair _ _ ihA ihB =>
      cases pure with
      | pair pureA pureB =>
          obtain ⟨rfl, evalA⟩ := ihA pureA
          obtain ⟨rfl, evalB⟩ := ihB pureB
          exact ⟨rfl, .pair evalA evalB⟩
  | call j θ _ matched _ ihA ihR =>
      cases pure with
      | call pureA =>
          obtain ⟨rfl, evalA⟩ := ihA pureA
          obtain ⟨rfl, evalR⟩ := ihR (instE_pure θ _)
          exact ⟨rfl, .call j θ evalA matched evalR⟩
  | bind => cases pure
  | read => cases pure
  | force => cases pure

theorem value_pure {H H' : Heap} {e : NEx} {v : Sx} (eval : VEval prog H e H' v) (pure : Pure e) :
    H' = H ∧ PEval prog e v := by
  induction eval with
  | val H t => exact ⟨rfl, .val t⟩
  | pair _ _ ihA ihB =>
      cases pure with
      | pair pureA pureB =>
          obtain ⟨rfl, evalA⟩ := ihA pureA
          obtain ⟨rfl, evalB⟩ := ihB pureB
          exact ⟨rfl, .pair evalA evalB⟩
  | call j θ _ matched _ ihA ihR =>
      cases pure with
      | call pureA =>
          obtain ⟨rfl, evalA⟩ := ihA pureA
          obtain ⟨rfl, evalR⟩ := ihR (instE_pure θ _)
          exact ⟨rfl, .call j θ evalA matched evalR⟩
  | bind => cases pure
  | read => cases pure

theorem pure_need {e : NEx} {v : Sx} (eval : PEval prog e v) (H : Heap) : NEval prog H e H v := by
  induction eval with
  | val t => exact .val H t
  | pair _ _ ihA ihB => exact .pair ihA ihB
  | call j θ _ matched _ ihA ihR => exact .call j θ ihA matched ihR

theorem pure_value {e : NEx} {v : Sx} (eval : PEval prog e v) (H : Heap) : VEval prog H e H v := by
  induction eval with
  | val t => exact .val H t
  | pair _ _ ihA ihB => exact .pair ihA ihB
  | call j θ _ matched _ ihA ihR => exact .call j θ ihA matched ihR

variable (prog) in
/-- **Determinate**: no data matches two equations, and a match fixes the instantiated right-hand
side. -/
def Determinate : Prop :=
  ∀ (j j' : Fin prog.length) (θ θ' : ℕ → Sx), (prog.get j).lhs.inst θ = (prog.get j').lhs.inst θ' →
    j = j' ∧ instE θ (prog.get j).rhs = instE θ' (prog.get j').rhs

theorem peval_unique (det : Determinate prog) {e : NEx} {v : Sx} (eval : PEval prog e v) :
    ∀ {v' : Sx}, PEval prog e v' → v = v' := by
  induction eval with
  | val t => intro v' other; cases other; rfl
  | pair _ _ ihA ihB =>
      intro v' other
      cases other with
      | pair otherA otherB => rw [ihA otherA, ihB otherB]
  | call j θ _ matched _ ihA ihR =>
      intro v' other
      cases other with
      | call j' θ' otherA matched' otherR =>
          have sameArg := ihA otherA
          subst sameArg
          obtain ⟨rfl, sameRhs⟩ := det j j' θ θ' (matched.trans matched'.symm)
          rw [sameRhs] at ihR
          exact ihR otherR

/-! ## Bound thunks that are pure and terminate -/

variable (prog) in
/-- Every bound thunk is pure and has a value. -/
inductive Thunks : NEx → Prop
  | val (t : Sx) : Thunks (.val t)
  | loc (ℓ : ℕ) : Thunks (.loc ℓ)
  | pair {a b : NEx} (left : Thunks a) (right : Thunks b) : Thunks (.pair a b)
  | call {a : NEx} (argument : Thunks a) : Thunks (.call a)
  | bind {ℓ : ℕ} {a b : NEx} (pure : Pure a) (terminates : ∃ v, PEval prog a v) (body : Thunks b) :
      Thunks (.bind ℓ a b)

theorem thunks_of_pure {e : NEx} (pure : Pure e) : Thunks prog e := by
  induction pure with
  | val t => exact .val t
  | pair _ _ ihA ihB => exact .pair ihA ihB
  | call _ ih => exact .call ih

/-! ## Related heaps -/

variable (prog) in
/-- **The by-value heap and the by-need heap agree cell by cell**: a by-need thunk is pure, and its
value is the by-value cell's. -/
structure Related (Hv Hn : Heap) : Prop where
  empty : ∀ ℓ, Hv ℓ = .empty ↔ Hn ℓ = .empty
  value : ∀ ℓ v, Hn ℓ = .value v → Hv ℓ = .value v
  thunk : ∀ ℓ a, Hn ℓ = .thunk a → Pure a ∧ ∃ v, PEval prog a v ∧ Hv ℓ = .value v
  back : ∀ ℓ v, Hv ℓ = .value v → Hn ℓ = .value v ∨ ∃ a, Hn ℓ = .thunk a ∧ Pure a ∧ PEval prog a v

theorem related_none : Related prog Heap.none Heap.none :=
  ⟨fun _ => Iff.rfl, (fun _ _ stored => by cases stored), (fun _ _ stored => by cases stored),
    (fun _ _ stored => by cases stored)⟩

theorem related_bind {Hv Hn : Heap} (related : Related prog Hv Hn) {ℓ : ℕ} {a : NEx} {va : Sx}
    (pure : Pure a) (eval : PEval prog a va) :
    Related prog (Hv.set ℓ (.value va)) (Hn.set ℓ (.thunk a)) := by
  refine ⟨fun ℓ' => ?_, fun ℓ' v stored => ?_, fun ℓ' a' stored => ?_, fun ℓ' v stored => ?_⟩
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same, Heap.set_same]
      constructor <;> intro h <;> cases h
    · rw [Heap.set_other _ _ same, Heap.set_other _ _ same]
      exact related.empty ℓ'
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same] at stored
      cases stored
    · rw [Heap.set_other _ _ same] at stored
      rw [Heap.set_other _ _ same]
      exact related.value ℓ' v stored
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same] at stored
      cases stored
      exact ⟨pure, va, eval, Heap.set_same _ _ _⟩
    · rw [Heap.set_other _ _ same] at stored
      rw [Heap.set_other _ _ same]
      exact related.thunk ℓ' a' stored
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same] at stored
      cases stored
      exact .inr ⟨a, Heap.set_same _ _ _, pure, eval⟩
    · rw [Heap.set_other _ _ same] at stored
      rw [Heap.set_other _ _ same]
      exact related.back ℓ' v stored

theorem related_force {Hv Hn : Heap} (related : Related prog Hv Hn) {ℓ : ℕ} {v : Sx}
    (stored : Hv ℓ = .value v) : Related prog Hv (Hn.set ℓ (.value v)) := by
  refine ⟨fun ℓ' => ?_, fun ℓ' w stored' => ?_, fun ℓ' a' stored' => ?_, fun ℓ' w stored' => ?_⟩
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same, stored]
    · rw [Heap.set_other _ _ same]
      exact related.empty ℓ'
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same] at stored'
      cases stored'
      exact stored
    · rw [Heap.set_other _ _ same] at stored'
      exact related.value ℓ' w stored'
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [Heap.set_same] at stored'
      cases stored'
    · rw [Heap.set_other _ _ same] at stored'
      exact related.thunk ℓ' a' stored'
  · by_cases same : ℓ' = ℓ
    · subst same
      rw [stored] at stored'
      cases stored'
      exact .inl (Heap.set_same _ _ _)
    · rw [Heap.set_other _ _ same]
      exact related.back ℓ' w stored'

/-! ## The two strategies agree -/

/-- **Every by-value answer is a by-need answer.** -/
theorem value_to_need {Hv Hv' : Heap} {e : NEx} {v : Sx} (eval : VEval prog Hv e Hv' v) :
    Thunks prog e → ∀ {Hn : Heap}, Related prog Hv Hn → ∃ Hn', NEval prog Hn e Hn' v ∧ Related prog Hv' Hn' := by
  induction eval with
  | val H t => exact fun _ Hn related => ⟨Hn, .val Hn t, related⟩
  | pair _ _ ihA ihB =>
      intro thunks Hn related
      cases thunks with
      | pair thunksA thunksB =>
          obtain ⟨Hn₁, evalA, related₁⟩ := ihA thunksA related
          obtain ⟨Hn₂, evalB, related₂⟩ := ihB thunksB related₁
          exact ⟨Hn₂, .pair evalA evalB, related₂⟩
  | call j θ _ matched _ ihA ihR =>
      intro thunks Hn related
      cases thunks with
      | call thunksA =>
          obtain ⟨Hn₁, evalA, related₁⟩ := ihA thunksA related
          obtain ⟨Hn₂, evalR, related₂⟩ := ihR (thunks_of_pure (instE_pure θ _)) related₁
          exact ⟨Hn₂, .call j θ evalA matched evalR, related₂⟩
  | bind thunk fresh _ _ ihB =>
      intro thunks Hn related
      cases thunks with
      | bind pure _ thunksB =>
          obtain ⟨rfl, evalA⟩ := value_pure thunk pure
          have freshN := (related.empty _).mp fresh
          obtain ⟨Hn', evalB, related'⟩ := ihB thunksB (related_bind related pure evalA)
          exact ⟨Hn', .bind freshN evalB, related'⟩
  | read stored =>
      intro _ Hn related
      rcases related.back _ _ stored with value | ⟨a, thunk, pure, evalA⟩
      · exact ⟨Hn, .read value, related⟩
      · refine ⟨(Hn.set _ .busy).set _ (.value _), .force thunk (pure_need evalA _), ?_⟩
        rw [Heap.set_set]
        exact related_force related stored

/-- **Every by-need answer is a by-value answer**, for a determinate program whose bound thunks
terminate. -/
theorem need_to_value (det : Determinate prog) {Hn Hn' : Heap} {e : NEx} {v : Sx} (eval : NEval prog Hn e Hn' v) :
    Thunks prog e → ∀ {Hv : Heap}, Related prog Hv Hn → ∃ Hv', VEval prog Hv e Hv' v ∧ Related prog Hv' Hn' := by
  induction eval with
  | val H t => exact fun _ Hv related => ⟨Hv, .val Hv t, related⟩
  | pair _ _ ihA ihB =>
      intro thunks Hv related
      cases thunks with
      | pair thunksA thunksB =>
          obtain ⟨Hv₁, evalA, related₁⟩ := ihA thunksA related
          obtain ⟨Hv₂, evalB, related₂⟩ := ihB thunksB related₁
          exact ⟨Hv₂, .pair evalA evalB, related₂⟩
  | call j θ _ matched _ ihA ihR =>
      intro thunks Hv related
      cases thunks with
      | call thunksA =>
          obtain ⟨Hv₁, evalA, related₁⟩ := ihA thunksA related
          obtain ⟨Hv₂, evalR, related₂⟩ := ihR (thunks_of_pure (instE_pure θ _)) related₁
          exact ⟨Hv₂, .call j θ evalA matched evalR, related₂⟩
  | bind fresh _ ihB =>
      intro thunks Hv related
      cases thunks with
      | bind pure terminates thunksB =>
          obtain ⟨va, evalA⟩ := terminates
          have freshV := (related.empty _).mpr fresh
          obtain ⟨Hv', evalB, related'⟩ := ihB thunksB (related_bind related pure evalA)
          exact ⟨Hv', .bind (pure_value evalA Hv) freshV evalB, related'⟩
  | read stored =>
      intro _ Hv related
      exact ⟨Hv, .read (related.value _ _ stored), related⟩
  | force stored inner _ =>
      intro _ Hv related
      obtain ⟨pure, v₀, eval₀, storedV⟩ := related.thunk _ _ stored
      obtain ⟨rfl, evalE⟩ := need_pure inner pure
      have same := peval_unique det evalE eval₀
      subst same
      refine ⟨Hv, .read storedV, ?_⟩
      rw [Heap.set_set]
      exact related_force related storedV

/-- **Call by need and call by value agree** on the answers of determinate programs whose bound
thunks are pure and terminate. -/
theorem need_value_agree (det : Determinate prog) {e : NEx} (thunks : Thunks prog e) (v : Sx) :
    (∃ H', VEval prog Heap.none e H' v) ↔ (∃ H', NEval prog Heap.none e H' v) := by
  constructor
  · rintro ⟨H', eval⟩
    obtain ⟨Hn', evalN, -⟩ := value_to_need eval thunks related_none
    exact ⟨Hn', evalN⟩
  · rintro ⟨H', eval⟩
    obtain ⟨Hv', evalV, -⟩ := need_to_value det eval thunks related_none
    exact ⟨Hv', evalV⟩

/-! ## Controls -/

section Controls

/-- `(= l (call l))`: the call `l` never returns. -/
def loopProg : Program := [⟨.sym 10, .call (.val (.sym 10))⟩]

/-- `bind 0 (call l) c`: the thunk is never demanded. -/
def loopBind : NEx := .bind 0 (.call (.val (.sym 10))) (.val (.sym 11))

/-- **By need, the program answers `c`.** -/
theorem need_answers_loop : NEval loopProg Heap.none loopBind (Heap.none.set 0 (.thunk (.call (.val (.sym 10)))))
    (.sym 11) :=
  .bind rfl (.val _ _)

theorem need_machine_loop : Relation.ReflTransGen (NStep loopProg) (.ev loopBind, [], Heap.none)
    (.ret (.sym 11), [], Heap.none.set 0 (.thunk (.call (.val (.sym 10))))) :=
  eval_runs need_answers_loop []

/-- The call `l` has no value by value. -/
theorem loop_no_value {H H' : Heap} {e : NEx} {v : Sx} (eval : VEval loopProg H e H' v) :
    e ≠ .call (.val (.sym 10)) := by
  induction eval with
  | val => exact fun same => by cases same
  | pair => exact fun same => by cases same
  | call j θ _ _ _ _ ihR =>
      intro _
      rcases j with ⟨_ | k, hk⟩
      · exact ihR rfl
      · exact absurd hk (by simp [loopProg])
  | bind => exact fun same => by cases same
  | read => exact fun same => by cases same

/-- **By value, the program has no answer**: the thunk is evaluated first and never returns. -/
theorem value_diverges_loop (H' : Heap) (v : Sx) : ¬ VEval loopProg Heap.none loopBind H' v := by
  intro eval
  cases eval with
  | bind thunk _ _ => exact loop_no_value thunk rfl

/-- `(= (g $x) (pair x x))`. -/
def shareProg : Program := [⟨.cell (.sym 20) (.var 0), .pair (.val (.var 0)) (.val (.var 0))⟩]

/-- `bind 0 (call (g c)) (pair 0 0)`: two demands of one thunk. -/
def shareBind : NEx := .bind 0 (.call (.val (.cell (.sym 20) (.sym 21)))) (.pair (.loc 0) (.loc 0))

theorem share_call : PEval shareProg (.call (.val (.cell (.sym 20) (.sym 21)))) (.cell (.sym 21) (.sym 21)) :=
  .call ⟨0, by decide⟩ (fun _ => .sym 21) (.val _) rfl (.pair (.val _) (.val _))

/-- **The thunk is forced by the first demand and read by the second.** -/
theorem shared_thunk_once :
    NEval shareProg Heap.none shareBind
      (((Heap.none.set 0 (.thunk (.call (.val (.cell (.sym 20) (.sym 21)))))).set 0 .busy).set 0
        (.value (.cell (.sym 21) (.sym 21))))
      (.cell (.cell (.sym 21) (.sym 21)) (.cell (.sym 21) (.sym 21))) :=
  .bind rfl (.pair (.force (Heap.set_same _ _ _) (pure_need share_call _)) (.read (Heap.set_same _ _ _)))

theorem shareProg_determinate : Determinate shareProg := by
  intro j j' θ θ' same
  rcases j with ⟨_ | k, hk⟩
  · rcases j' with ⟨_ | k', hk'⟩
    · refine ⟨rfl, ?_⟩
      change Pat.inst θ (.cell (.sym 20) (.var 0)) = Pat.inst θ' (.cell (.sym 20) (.var 0)) at same
      have parts : θ 0 = θ' 0 := by
        simp only [Pat.inst, Sx.cell.injEq, true_and] at same
        exact same
      change instE θ (.pair (.val (.var 0)) (.val (.var 0))) = instE θ' (.pair (.val (.var 0)) (.val (.var 0)))
      simp only [instE, Pat.inst, parts]
    · exact absurd hk' (by simp [shareProg])
  · exact absurd hk (by simp [shareProg])

theorem share_thunks : Thunks shareProg shareBind :=
  .bind (.call (.val _)) ⟨_, share_call⟩ (.pair (.loc 0) (.loc 0))

/-- By value, the same answer. -/
theorem share_by_value : ∃ H', VEval shareProg Heap.none shareBind H' (.cell (.cell (.sym 21) (.sym 21))
    (.cell (.sym 21) (.sym 21))) :=
  (need_value_agree shareProg_determinate share_thunks _).mpr ⟨_, shared_thunk_once⟩

end Controls

#print axioms need_pure
#print axioms peval_unique
#print axioms related_bind
#print axioms related_force
#print axioms value_to_need
#print axioms need_to_value
#print axioms need_value_agree
#print axioms need_answers_loop
#print axioms need_machine_loop
#print axioms value_diverges_loop
#print axioms shared_thunk_once
#print axioms shareProg_determinate
#print axioms share_by_value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed
