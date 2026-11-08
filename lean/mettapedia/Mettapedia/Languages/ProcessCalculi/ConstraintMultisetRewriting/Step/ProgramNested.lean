import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedMatcher

/-!
# Nested calls on the step: the frame-stack machine compiled into schemas

Each rule of the frame-stack machine (`ProgramNestedSource.KStep`) becomes one schema
(`kschema`): six administrative schemas, one schema per equation of each version (take the call
with its continuation, read the version row, make the instantiated right-hand side under the
continuation and the citation), and one redefinition schema per pair of versions. Every firing is a
firing of the ordinary step: no guard, no predicate query.

* **Soundness** (`nested_sound`): every machine step from rows represented on the step is matched
  by one admitted firing, whose result represents the machine's result.
* **Completeness** (`nested_complete`): every admitted firing from represented well-formed rows is
  the image of one machine step, and its result represents that step's result.
* **Runs** (`nested_execution`): from the initial configuration, machine runs and runs of
  translated firings reach the same rows, read through solved forms, in both directions.

So, through `kruns_unload`, every translated run is a run of the reference semantics in evaluation
contexts. The administrative firings bind only their own fresh variables (`matcher_fixes`), so they
never touch the caller's rows; only answering a call binds the caller's variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions

/-! ## The machine's patterns and schemas -/

def pev (e k : Pat) : Pat := ptag 120 (.cell e k)
def pret (v k : Pat) : Pat := ptag 121 (.cell v k)
def pap (w k : Pat) : Pat := ptag 122 (.cell w k)
def pval (p : Pat) : Pat := ptag 130 p
def ppair (a b : Pat) : Pat := ptag 131 (.cell a b)
def pcall (a : Pat) : Pat := ptag 132 a
def pleft (b k : Pat) : Pat := ptag 140 (.cell b k)
def pright (v k : Pat) : Pat := ptag 141 (.cell v k)
def parg (k : Pat) : Pat := ptag 142 k

/-- The continuation's name in an equation's schema: outside the equation's variables. -/
def kname (e : NEquation) : ℕ := (e.lhs.vars ++ e.rhs.vars).sum + 1

theorem lt_sum_succ : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x < l.sum + 1
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [List.sum_cons]
        omega
      · have := lt_sum_succ h
        simp only [List.sum_cons]
        omega

theorem kname_lhs (e : NEquation) : kname e ∉ e.lhs.vars := fun h => by
  have := lt_sum_succ (List.mem_append_left e.rhs.vars h)
  unfold kname at this
  omega

theorem kname_rhs (e : NEquation) : kname e ∉ e.rhs.vars := fun h => by
  have := lt_sum_succ (List.mem_append_right e.lhs.vars h)
  unfold kname at this
  omega

/-- The rules of the machine. -/
inductive KRule (defs : Defs) where
  | val
  | pair
  | call
  | left
  | right
  | arg
  | apply (u : ℕ) (j : Fin (defs u).length)
  | redefine (u u' : ℕ)

/-- **The compiled machine**: one schema per rule. -/
def kschema (defs : Defs) : KRule defs → Schema
  | .val => ⟨[pev (pval (.var 0)) (.var 1)], [], [pret (.var 0) (.var 1)]⟩
  | .pair => ⟨[pev (ppair (.var 0) (.var 1)) (.var 2)], [], [pev (.var 0) (pleft (.var 1) (.var 2))]⟩
  | .call => ⟨[pev (pcall (.var 0)) (.var 1)], [], [pev (.var 0) (parg (.var 1))]⟩
  | .left => ⟨[pret (.var 0) (pleft (.var 1) (.var 2))], [], [pev (.var 1) (pright (.var 0) (.var 2))]⟩
  | .right => ⟨[pret (.var 1) (pright (.var 0) (.var 2))], [], [pret (.cell (.var 0) (.var 1)) (.var 2)]⟩
  | .arg => ⟨[pret (.var 0) (parg (.var 1))], [], [pap (.var 0) (.var 1)]⟩
  | .apply u j => ⟨[pap ((defs u).get j).lhs (.var (kname ((defs u).get j)))], [ptag 41 (.sym u)],
      [pev (EPat.enc ((defs u).get j).rhs) (.var (kname ((defs u).get j))), ptag 42 (.sym u)]⟩
  | .redefine u u' => ⟨[ptag 123 (.sym u'), ptag 41 (.sym u)], [], [ptag 124 (.sym 0), ptag 41 (.sym u')]⟩

/-! ## Well-formed rows and their shapes -/

/-- The tags the machine reads or makes. -/
def machineTag (k : ℕ) : Prop := k = 41 ∨ k = 42 ∨ k = 120 ∨ k = 121 ∨ k = 122 ∨ k = 123 ∨ k = 124

/-- **Well-formed source rows**: data rows carry a tag the machine never reads or makes. -/
def SRow.Good : SRow → Prop
  | .data k _ => ¬ machineTag k
  | _ => True

theorem SRow.Good.subst {s : SRow} (good : s.Good) (θ : Subst rows) : (s.subst θ).Good := by
  cases s <;> exact good

def SRow.tag : SRow → ℕ
  | .ev _ _ => 120
  | .ret _ _ => 121
  | .ap _ _ => 122
  | .version _ => 41
  | .citation _ => 42
  | .redef _ => 123
  | .finished => 124
  | .data k _ => k

def SRow.body : SRow → Tm
  | .ev e K => node (encE e) (encK K)
  | .ret v K => node v (encK K)
  | .ap w K => node w (encK K)
  | .version u => .const u
  | .citation u => .const u
  | .redef u => .const u
  | .finished => .const 0
  | .data _ t => t

theorem SRow.enc_eq : ∀ s : SRow, s.enc = tagged s.tag s.body
  | .ev _ _ => rfl
  | .ret _ _ => rfl
  | .ap _ _ => rfl
  | .version _ => rfl
  | .citation _ => rfl
  | .redef _ => rfl
  | .finished => rfl
  | .data _ _ => rfl

theorem tag_forced {σ : Subst rows} {k : ℕ} {X : Tm} {s : SRow}
    (same : σ.applyTerm (tagged k X) = σ.applyTerm s.enc) :
    k = s.tag ∧ σ.applyTerm X = σ.applyTerm s.body := by
  rw [SRow.enc_eq, apply_tagged, apply_tagged, tagged_inj] at same
  exact same

theorem node_forced {σ : Subst rows} {a b c d : Tm}
    (same : σ.applyTerm (node a b) = σ.applyTerm (node c d)) :
    σ.applyTerm a = σ.applyTerm c ∧ σ.applyTerm b = σ.applyTerm d := by
  rw [apply_node, apply_node, node_inj] at same
  exact same

theorem good_ev {s : SRow} (good : s.Good) (h : 120 = s.tag) : ∃ e K, s = .ev e K := by
  cases s <;> simp_all [SRow.tag, SRow.Good, machineTag]

theorem good_ret {s : SRow} (good : s.Good) (h : 121 = s.tag) : ∃ v K, s = .ret v K := by
  cases s <;> simp_all [SRow.tag, SRow.Good, machineTag]

theorem good_ap {s : SRow} (good : s.Good) (h : 122 = s.tag) : ∃ w K, s = .ap w K := by
  cases s <;> simp_all [SRow.tag, SRow.Good, machineTag]

theorem good_version {s : SRow} (good : s.Good) (h : 41 = s.tag) : ∃ u, s = .version u := by
  cases s <;> simp_all [SRow.tag, SRow.Good, machineTag]

theorem good_redef {s : SRow} (good : s.Good) (h : 123 = s.tag) : ∃ u, s = .redef u := by
  cases s <;> simp_all [SRow.tag, SRow.Good, machineTag]

theorem const_forced {σ : Subst rows} {k k' : ℕ}
    (same : σ.applyTerm (.const k) = σ.applyTerm (.const k')) : k = k' := by
  rw [Subst.applyTerm_const, Subst.applyTerm_const] at same
  cases same
  rfl

theorem ex_forced {σ : Subst rows} {k : ℕ} {X : Tm} {e : Ex}
    (same : σ.applyTerm (tagged k X) = σ.applyTerm (encE e)) :
    (k = 130 ∧ ∃ t, e = .val t) ∨
    (k = 131 ∧ ∃ a b, e = .pair a b ∧ σ.applyTerm X = σ.applyTerm (node (encE a) (encE b))) ∨
    (k = 132 ∧ ∃ a, e = .call a ∧ σ.applyTerm X = σ.applyTerm (encE a)) := by
  cases e with
  | val t =>
      rw [encE, apply_tagged, apply_tagged, tagged_inj] at same
      exact .inl ⟨same.1, t, rfl⟩
  | pair a b =>
      rw [encE, apply_tagged, apply_tagged, tagged_inj] at same
      exact .inr (.inl ⟨same.1, a, b, rfl, same.2⟩)
  | call a =>
      rw [encE, apply_tagged, apply_tagged, tagged_inj] at same
      exact .inr (.inr ⟨same.1, a, rfl, same.2⟩)

theorem frame_forced {σ : Subst rows} {k : ℕ} {X : Tm} {K : List Frame}
    (same : σ.applyTerm (tagged k X) = σ.applyTerm (encK K)) :
    (k = 140 ∧ ∃ b K', K = .left b :: K') ∨
    (k = 141 ∧ ∃ v K', K = .right v :: K') ∨
    (k = 142 ∧ ∃ K', K = .arg :: K') := by
  match K with
  | [] =>
      rw [encK, apply_tagged, Subst.applyTerm_const] at same
      exact absurd same node_ne_const
  | .left b :: K' =>
      rw [encK, apply_tagged, apply_tagged, tagged_inj] at same
      exact .inl ⟨same.1, b, K', rfl⟩
  | .right v :: K' =>
      rw [encK, apply_tagged, apply_tagged, tagged_inj] at same
      exact .inr (.inl ⟨same.1, v, K', rfl⟩)
  | .arg :: K' =>
      rw [encK, apply_tagged, apply_tagged, tagged_inj] at same
      exact .inr (.inr ⟨same.1, K', rfl⟩)

/-! ## Bookkeeping -/

/-- Rows read from a represented configuration name only earlier scopes. -/
theorem rep_bounded {C : Config} {W : Multiset Tm} {n : ℕ} (rep : ORepresents C W n) :
    ∀ t ∈ W, Bounded n t := by
  obtain ⟨μ, solved, rfl⟩ := rep
  intro t member
  obtain ⟨o, oIn, rfl⟩ := Multiset.mem_map.mp member
  exact solved.read_bounded (solved.occurrences o oIn).2

/-- Removing a represented occurrence removes its source row. -/
theorem erase_image {P : Finset Occ} {f : Occ → Tm} {Ws : Multiset SRow}
    (image : P.val.map f = Ws.map SRow.enc) {o : Occ} (oIn : o ∈ P) {s : SRow} (sIn : s ∈ Ws)
    (reads : f o = s.enc) : (P.erase o).val.map f = (Ws.erase s).map SRow.enc := by
  have one : P.val = o ::ₘ (P.erase o).val := by rw [Finset.erase_val, Multiset.cons_erase oIn]
  have two : Ws = s ::ₘ Ws.erase s := (Multiset.cons_erase sIn).symm
  rw [one, Multiset.map_cons, reads] at image
  rw [two, Multiset.map_cons] at image
  exact (Multiset.cons_inj_right _).mp image

/-- A represented occurrence reads as a source row. -/
theorem read_source {P : Finset Occ} {f : Occ → Tm} {Ws : Multiset SRow}
    (image : P.val.map f = Ws.map SRow.enc) {o : Occ} (oIn : o ∈ P) : ∃ s ∈ Ws, f o = s.enc := by
  have : f o ∈ Ws.map SRow.enc := by
    rw [← image]
    exact Multiset.mem_map_of_mem f oIn
  obtain ⟨s, sIn, same⟩ := Multiset.mem_map.mp this
  exact ⟨s, sIn, same.symm⟩

/-- What an admitted firing says about its selection. -/
theorem valid_shape {C : Config} {n : ℕ} {r : Schema} {taken read : List Occ}
    (valid : (r.firing n taken read).Valid A Occ.label C) :
    taken.Nodup ∧ (∀ o ∈ taken, o ∈ C.present) ∧ (∀ o ∈ read, o ∈ C.present) ∧
      (∀ o ∈ taken, o ∉ read) ∧ r.take.length = taken.length ∧ r.read.length = read.length := by
  refine ⟨valid.firing.take_distinct, fun o h =>
    valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr h), fun o h =>
    valid.firing.occurrences.kept_subset (List.mem_toFinset.mpr h), fun o h h' =>
    Finset.disjoint_left.mp valid.firing.occurrences.apart (List.mem_toFinset.mpr h)
      (List.mem_toFinset.mpr h'), ?_, ?_⟩
  · have h : (r.take.map (Pat.at n)).length = taken.length := valid.firing.take_length
    rwa [List.length_map] at h
  · have h : (r.read.map (Pat.at n)).length = read.length := valid.firing.read_length
    rwa [List.length_map] at h

/-! ## Firings on one, two, or a taken and a read row -/

/-- **A firing taking one row**, for a most general unifier of its pattern with the row. -/
theorem fire_one {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o : Occ} (oIn : o ∈ C.present) {s : SRow} (sIn : s ∈ Ws) (reads : readAt μ o = s.enc)
    {r : Schema} {p : Pat} (take : r.take = [p]) (read : r.read = [])
    {θ : Subst rows} (mgu : IsMGU [(p.at n, s.enc)] θ) :
    (r.firing n [o] []).Valid A Occ.label C ∧
    ORepresents ((r.firing n [o] []).result Occ.label C)
      (((r.make.map fun q => θ.applyTerm (q.at n) : List Tm) : Multiset Tm) +
        ((Ws.erase s).map SRow.enc).map θ.applyTerm) (n + 1) := by
  have problem : schemaProblem r n μ [o] [] = [(p.at n, s.enc)] := by
    unfold schemaProblem problem
    rw [take, read]
    simp [reads]
  obtain ⟨valid, solved', rows⟩ := ofire_at (r := r) (taken := [o]) (read := []) solved
    (List.nodup_singleton o) (fun x h => by rw [List.mem_singleton.mp h]; exact oIn)
    (fun x h => absurd h List.not_mem_nil) (fun x _ h => absurd h List.not_mem_nil)
    (by rw [take]; rfl) (by rw [read]; rfl) (problem ▸ mgu)
  refine ⟨valid, θ ∘ₛ μ, solved', ?_⟩
  rw [rows, sdiff_singleton, erase_image image oIn sIn reads, add_comm]

/-- **A firing taking one row and reading another.** -/
theorem fire_take_read {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o o' : Occ} (oIn : o ∈ C.present) (o'In : o' ∈ C.present) (apart : o ≠ o')
    {s s' : SRow} (sIn : s ∈ Ws) (reads : readAt μ o = s.enc) (reads' : readAt μ o' = s'.enc)
    {r : Schema} {p p' : Pat} (take : r.take = [p]) (read : r.read = [p'])
    {θ : Subst rows} (mgu : IsMGU [(p.at n, s.enc), (p'.at n, s'.enc)] θ) :
    (r.firing n [o] [o']).Valid A Occ.label C ∧
    ORepresents ((r.firing n [o] [o']).result Occ.label C)
      (((r.make.map fun q => θ.applyTerm (q.at n) : List Tm) : Multiset Tm) +
        ((Ws.erase s).map SRow.enc).map θ.applyTerm) (n + 1) := by
  have problem : schemaProblem r n μ [o] [o'] = [(p.at n, s.enc), (p'.at n, s'.enc)] := by
    unfold schemaProblem problem
    rw [take, read]
    simp [reads, reads']
  obtain ⟨valid, solved', rows⟩ := ofire_at (r := r) (taken := [o]) (read := [o']) solved
    (List.nodup_singleton o) (fun x h => by rw [List.mem_singleton.mp h]; exact oIn)
    (fun x h => by rw [List.mem_singleton.mp h]; exact o'In)
    (fun x h h' => by
      rw [List.mem_singleton] at h h'
      exact apart (h.symm.trans h'))
    (by rw [take]; rfl) (by rw [read]; rfl) (problem ▸ mgu)
  refine ⟨valid, θ ∘ₛ μ, solved', ?_⟩
  rw [rows, sdiff_singleton, erase_image image oIn sIn reads, add_comm]

/-- **A firing taking two rows.** -/
theorem fire_two {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o o' : Occ} (oIn : o ∈ C.present) (o'In : o' ∈ C.present) (apart : o ≠ o')
    {s s' : SRow} (sIn : s ∈ Ws) (s'In : s' ∈ Ws.erase s) (reads : readAt μ o = s.enc)
    (reads' : readAt μ o' = s'.enc)
    {r : Schema} {p p' : Pat} (take : r.take = [p, p']) (read : r.read = [])
    {θ : Subst rows} (mgu : IsMGU [(p.at n, s.enc), (p'.at n, s'.enc)] θ) :
    (r.firing n [o, o'] []).Valid A Occ.label C ∧
    ORepresents ((r.firing n [o, o'] []).result Occ.label C)
      (((r.make.map fun q => θ.applyTerm (q.at n) : List Tm) : Multiset Tm) +
        (((Ws.erase s).erase s').map SRow.enc).map θ.applyTerm) (n + 1) := by
  have problem : schemaProblem r n μ [o, o'] [] = [(p.at n, s.enc), (p'.at n, s'.enc)] := by
    unfold schemaProblem problem
    rw [take, read]
    simp [reads, reads']
  have takenIn : ∀ x ∈ [o, o'], x ∈ C.present := by
    intro x h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact oIn
    · exact o'In
  obtain ⟨valid, solved', rows⟩ := ofire_at (r := r) (taken := [o, o']) (read := []) solved
    (List.nodup_cons.mpr ⟨by simpa using apart, List.nodup_singleton o'⟩) takenIn
    (fun x h => absurd h List.not_mem_nil) (fun x _ h => absurd h List.not_mem_nil)
    (by rw [take]; rfl) (by rw [read]; rfl) (problem ▸ mgu)
  refine ⟨valid, θ ∘ₛ μ, solved', ?_⟩
  have sdiff : C.present \ [o, o'].toFinset = (C.present.erase o).erase o' := by
    rw [List.toFinset_cons, Finset.sdiff_insert, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.sdiff_singleton_eq_erase, Finset.erase_right_comm]
  have first := erase_image image oIn sIn reads
  have o'In' : o' ∈ C.present.erase o := Finset.mem_erase.mpr ⟨fun h => apart h.symm, o'In⟩
  rw [rows, sdiff, erase_image first o'In' s'In reads', add_comm]

/-! ## The rows a firing makes -/

theorem single_read (defs : Defs) (i : KRule defs) : (kschema defs i).read.length ≤ 1 := by
  cases i <;> simp [kschema]

/-- A source row of a represented configuration is read by one of its occurrences. -/
theorem pick_source {P : Finset Occ} {f : Occ → Tm} {Ws : Multiset SRow}
    (image : P.val.map f = Ws.map SRow.enc) {s : SRow} (sIn : s ∈ Ws) : ∃ o ∈ P, f o = s.enc := by
  have : s.enc ∈ P.val.map f := by
    rw [image]
    exact Multiset.mem_map_of_mem _ sIn
  obtain ⟨o, oIn, same⟩ := Multiset.mem_map.mp this
  exact ⟨o, oIn, same⟩

theorem image_bounded {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc) :
    ∀ s ∈ Ws, Bounded n s.enc := fun _ sIn =>
  rep_bounded ⟨μ, solved, image⟩ _ (Multiset.mem_map_of_mem _ sIn)

/-- **The rows of an administrative firing**: its made row, and the other rows untouched. -/
theorem admin_rows {n : ℕ} {vals : List Tm} {q : Pat} {k : ℕ} (length : vals.length = k)
    (withinq : ∀ x ∈ q.vars, x < k) {s' : SRow} (target : Pat.fill vals q = s'.enc)
    {F : Multiset SRow} (bounded : ∀ s ∈ F, Bounded n s.enc) :
    ((([q].map fun q => (matcher n vals).applyTerm (q.at n) : List Tm)) : Multiset Tm) +
        (F.map SRow.enc).map (matcher n vals).applyTerm = (s' ::ₘ F).map SRow.enc := by
  subst length
  have rest : (F.map SRow.enc).map (matcher n vals).applyTerm = F.map SRow.enc := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun s member => matcher_fixes (bounded s member)
  rw [rest, List.map_singleton, matcher_at q withinq, target, Multiset.map_cons]
  simp

/-- **The administrative firings, both ways**: an admitted firing of an administrative schema on a
row of the given shape represents that row's successor. -/
theorem admin_fire {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o : Occ} (oIn : o ∈ C.present) {s s' : SRow} (sIn : s ∈ Ws) (reads : readAt μ o = s.enc)
    {r : Schema} {p q : Pat} (take : r.take = [p]) (read : r.read = []) (make : r.make = [q])
    {vals : List Tm} {k : ℕ} (length : vals.length = k) (covers : ∀ x < k, x ∈ p.vars)
    (within : ∀ x ∈ p.vars, x < k) (withinq : ∀ x ∈ q.vars, x < k)
    (source : Pat.fill vals p = s.enc) (target : Pat.fill vals q = s'.enc) :
    (r.firing n [o] []).Valid A Occ.label C ∧
      ORepresents ((r.firing n [o] []).result Occ.label C) ((s' ::ₘ Ws.erase s).map SRow.enc)
        (n + 1) := by
  have bounded := image_bounded solved image
  have valsBounded := vals_bounded_of_fill (source ▸ bounded s sIn) (length ▸ covers)
  have mgu := matcher_isMGU valsBounded (length ▸ covers) (length ▸ within)
  rw [source] at mgu
  obtain ⟨valid, rep⟩ := fire_one solved image oIn sIn reads take read mgu
  refine ⟨valid, ?_⟩
  rw [make, admin_rows length withinq target fun t member =>
    bounded t (Multiset.mem_of_mem_erase member)] at rep
  exact rep

/-! ## Answering a call -/

theorem at_vars {n : ℕ} : ∀ (p : Pat) {v : ℕ × ℕ}, v ∈ (p.at n).freeVars → v.2 ∈ p.vars
  | .var x, v, hv => by
      rw [Pat.at, Term.mem_freeVars_var (σ := rows)] at hv
      subst hv
      simp [Pat.vars]
  | .sym _, _, hv => by simp [Pat.at, Term.freeVars] at hv
  | .cell a b, v, hv => by
      rcases mem_freeVars_node.mp hv with hv | hv
      · exact List.mem_append_left _ (at_vars a hv)
      · exact List.mem_append_right _ (at_vars b hv)

theorem bounded_node {n : ℕ} {k : ℕ} {a b : Tm} (h : Bounded n (tagged k (node a b))) :
    Bounded n a ∧ Bounded n b := by
  refine ⟨fun v hv => h v ?_, fun v hv => h v ?_⟩
  · rw [freeVars_tagged, mem_freeVars_node]
    exact .inl hv
  · rw [freeVars_tagged, mem_freeVars_node]
    exact .inr hv

theorem pair_add {α : Type*} (a b : α) (M : Multiset α) :
    (([a, b] : List α) : Multiset α) + M = a ::ₘ b ::ₘ M := by
  show (a ::ₘ b ::ₘ 0) + M = _
  rw [Multiset.cons_add, Multiset.cons_add, zero_add]

theorem freeVars_node (a b : Tm) : (node a b).freeVars = a.freeVars ∪ b.freeVars := by
  ext v
  rw [mem_freeVars_node, Finset.mem_union]

theorem version_fixed (θ : Subst rows) (u : ℕ) : θ.applyTerm (SRow.version u).enc = (SRow.version u).enc := by
  show θ.applyTerm (tagged 41 (.const u)) = _
  rw [apply_tagged]
  rfl

/-- The selected problem of an equation's schema on a call and the version row. -/
def applyProblem (n : ℕ) (e : NEquation) (u : ℕ) (w : Tm) (K : List Frame) : List (Tm × Tm) :=
  [((pap e.lhs (.var (kname e))).at n, (SRow.ap w K).enc), ((ptag 41 (.sym u)).at n, (SRow.version u).enc)]

/-- **A most general unifier of the call, extended by the continuation, answers the schema's
problem.** -/
theorem apply_mgu {n : ℕ} {e : NEquation} {u : ℕ} {w : Tm} {K : List Frame} {θ : Subst rows}
    (mgu : IsMGU [(e.lhs.at n, w)] θ) (wB : Bounded n w) (KB : Bounded n (encK K)) :
    IsMGU (applyProblem n e u w K) (extendAt θ (n, kname e) (encK K)) := by
  have freshP : (n, kname e) ∉ eqVars [(e.lhs.at n, w)] := by
    intro h
    obtain ⟨pair, member, occurs⟩ := (mem_eqVars (σ := rows)).mp h
    rw [List.mem_singleton] at member
    subst member
    rcases occurs with occurs | occurs
    · exact kname_lhs e (at_vars e.lhs occurs)
    · exact absurd (wB _ occurs) (lt_irrefl n)
  have freshK : (n, kname e) ∉ (encK K).freeVars := fun h => absurd (KB _ h) (lt_irrefl n)
  have ext := isMGU_extend mgu freshP freshK
  refine ext.congr (fun δ => ?_) ?_
  · simp only [applyProblem, Unifies, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, pap, ptag_at, Pat.at, SRow.enc, ver, apply_tagged,
      tagged_inj, apply_node, node_inj, Subst.applyTerm_var, Subst.applyTerm_const, true_and,
      and_true]
    exact and_comm
  · ext x
    simp only [applyProblem, eqVars, pap, ptag_at, Pat.at, SRow.enc, ver, freeVars_tagged,
      Finset.mem_union, freeVars_node, Term.freeVars, Finset.mem_singleton,
      Finset.notMem_empty, or_false]
    tauto

/-- **The rows of an answered call.** -/
theorem apply_rows {n : ℕ} {e : NEquation} {u : ℕ} {K : List Frame} {θ : Subst rows}
    {F : Multiset SRow} (bounded : ∀ s ∈ F, Bounded n s.enc) :
    ((([pev (EPat.enc e.rhs) (.var (kname e)), ptag 42 (.sym u)].map fun q =>
        (extendAt θ (n, kname e) (encK K)).applyTerm (q.at n) : List Tm)) : Multiset Tm) +
      ((.version u ::ₘ F).map SRow.enc).map (extendAt θ (n, kname e) (encK K)).applyTerm =
    (.ev ((e.rhs.at n).subst θ) (K.map (Frame.subst θ)) ::ₘ .citation u ::ₘ .version u ::ₘ
      F.map (SRow.subst θ)).map SRow.enc := by
  have rhsFresh : (n, kname e) ∉ ((EPat.enc e.rhs).at n).freeVars := fun h => by
    have := at_vars _ h
    rw [EPat.enc_vars] at this
    exact kname_rhs e this
  have made : (extendAt θ (n, kname e) (encK K)).applyTerm ((pev (EPat.enc e.rhs) (.var (kname e))).at n) =
      (SRow.ev ((e.rhs.at n).subst θ) (K.map (Frame.subst θ))).enc := by
    rw [pev, ptag_at, apply_tagged, Pat.at, apply_node, Pat.at, Subst.applyTerm_var,
      extendAt_agree rhsFresh, extendAt, if_pos rfl, EPat.enc_at, ← encE_subst, ← encK_subst]
    rfl
  have rest : (F.map SRow.enc).map (extendAt θ (n, kname e) (encK K)).applyTerm =
      (F.map (SRow.subst θ)).map SRow.enc := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun s member => ?_
    simp only [Function.comp_apply]
    rw [extendAt_agree fun h => absurd (bounded s member _ h) (lt_irrefl n), SRow.enc_subst]
  rw [List.map_cons, List.map_singleton, made, Multiset.map_cons, Multiset.map_cons, rest]
  simp only [Multiset.map_cons]
  rw [ptag_at, apply_tagged, Pat.at, Subst.applyTerm_const, version_fixed,
    show tagged 42 (Term.const u) = (SRow.citation u).enc from rfl, pair_add]

/-- **Answering a call, both ways**: for any most general unifier of the call with the left-hand
side, the equation's firing on the call and the version row is admitted, and represents the
answer. -/
theorem apply_fire {defs : Defs} {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o o' : Occ} (oIn : o ∈ C.present) (o'In : o' ∈ C.present) (apart : o ≠ o')
    {u : ℕ} {j : Fin (defs u).length} {w : Tm} {K : List Frame} {F : Multiset SRow}
    (shape : Ws = .ap w K ::ₘ .version u ::ₘ F)
    (reads : readAt μ o = (SRow.ap w K).enc) (reads' : readAt μ o' = (SRow.version u).enc)
    {θ : Subst rows} (mgu : IsMGU [(((defs u).get j).lhs.at n, w)] θ) :
    ((kschema defs (.apply u j)).firing n [o] [o']).Valid A Occ.label C ∧
      ORepresents (((kschema defs (.apply u j)).firing n [o] [o']).result Occ.label C)
        ((.ev ((((defs u).get j).rhs.at n).subst θ) (K.map (Frame.subst θ)) ::ₘ .citation u ::ₘ
          .version u ::ₘ F.map (SRow.subst θ)).map SRow.enc) (n + 1) := by
  have bounded := image_bounded solved image
  have apBounded := bounded_node (bounded (.ap w K) (by rw [shape]; simp))
  have mgu' := apply_mgu (u := u) mgu apBounded.1 apBounded.2
  have sIn : SRow.ap w K ∈ Ws := by rw [shape]; simp
  obtain ⟨valid, rep⟩ := fire_take_read (r := kschema defs (.apply u j)) solved image oIn o'In apart sIn reads reads'
    rfl rfl mgu'
  refine ⟨valid, ?_⟩
  have erased : Ws.erase (.ap w K) = .version u ::ₘ F := by rw [shape, Multiset.erase_cons_head]
  rw [erased, show (kschema defs (.apply u j)).make =
    [pev (EPat.enc ((defs u).get j).rhs) (.var (kname ((defs u).get j))), ptag 42 (.sym u)] from rfl,
    apply_rows fun s member => bounded s (by rw [shape]; simp [member])] at rep
  exact rep

/-! ## Redefinition -/

theorem redefine_fire {defs : Defs} {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o o' : Occ} (oIn : o ∈ C.present) (o'In : o' ∈ C.present) (apart : o ≠ o')
    {u u' : ℕ} {F : Multiset SRow} (shape : Ws = .redef u' ::ₘ .version u ::ₘ F)
    (reads : readAt μ o = (SRow.redef u').enc) (reads' : readAt μ o' = (SRow.version u).enc) :
    ((kschema defs (.redefine u u')).firing n [o, o'] []).Valid A Occ.label C ∧
      ORepresents (((kschema defs (.redefine u u')).firing n [o, o'] []).result Occ.label C)
        ((.finished ::ₘ .version u' ::ₘ F).map SRow.enc) (n + 1) := by
  have sIn : SRow.redef u' ∈ Ws := by rw [shape]; simp
  have s'In : SRow.version u ∈ Ws.erase (.redef u') := by rw [shape, Multiset.erase_cons_head]; simp
  have mgu : IsMGU [((ptag 123 (.sym u')).at n, (SRow.redef u').enc),
      ((ptag 41 (.sym u)).at n, (SRow.version u).enc)] (Subst.id rows) :=
    isMGU_id_of_eq fun e member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
  obtain ⟨valid, rep⟩ := fire_two (r := kschema defs (.redefine u u')) solved image oIn o'In apart sIn s'In
    reads reads' rfl rfl mgu
  refine ⟨valid, ?_⟩
  have erased : (Ws.erase (.redef u')).erase (.version u) = F := by
    rw [shape, Multiset.erase_cons_head, Multiset.erase_cons_head]
  rw [erased] at rep
  have rows : ((((kschema defs (.redefine u u')).make.map fun q =>
      (Subst.id rows).applyTerm (q.at n) : List Tm)) : Multiset Tm) +
        (F.map SRow.enc).map (Subst.id rows).applyTerm =
      (.finished ::ₘ .version u' ::ₘ F).map SRow.enc := by
    have ident : (F.map SRow.enc).map (Subst.id rows).applyTerm = F.map SRow.enc := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun t _ => Subst.applyTerm_id _
    rw [ident]
    simp [kschema, Subst.applyTerm_id, SRow.enc, ver]
    refine (pair_add _ _ _).trans ?_
    rfl
  rw [rows] at rep
  exact rep

/-! ## Soundness and completeness -/

/-- **Soundness**: every machine step from represented rows is one admitted translated firing,
whose result represents the machine's result. -/
theorem nested_sound {defs : Defs} {C : Config} {Ws : Multiset SRow} {n : ℕ}
    (rep : ORepresents C (Ws.map SRow.enc) n) {s' : Multiset SRow × ℕ}
    (step : KStep defs (Ws, n) s') :
    ∃ D, Translated (kschema defs) (C, n) (D, s'.2) ∧ ORepresents D (s'.1.map SRow.enc) s'.2 := by
  obtain ⟨μ, solved, image⟩ := rep
  have head : ∀ {s : SRow} {F : Multiset SRow}, Ws = s ::ₘ F → ∃ o ∈ C.present, readAt μ o = s.enc :=
    fun shape => pick_source image (by rw [shape]; simp)
  cases step with
  | val t K F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      obtain ⟨valid, rep'⟩ := admin_fire (r := kschema defs .val) (vals := [t, encK K]) (k := 2)
        (s' := .ret t K) solved image
        oIn (Multiset.mem_cons_self _ _) reads rfl rfl rfl rfl (by decide) (by decide) (by decide) rfl rfl
      rw [Multiset.erase_cons_head] at rep'
      exact ⟨_, Translated.fire (schema := kschema defs) KRule.val [o] [] valid, rep'⟩
  | pair a b K F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      obtain ⟨valid, rep'⟩ := admin_fire (r := kschema defs .pair) (vals := [encE a, encE b, encK K]) (k := 3)
        (s' := .ev a (.left b :: K))
        solved image oIn (Multiset.mem_cons_self _ _) reads rfl rfl rfl rfl (by decide) (by decide)
        (by decide) rfl rfl
      rw [Multiset.erase_cons_head] at rep'
      exact ⟨_, Translated.fire (schema := kschema defs) KRule.pair [o] [] valid, rep'⟩
  | call a K F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      obtain ⟨valid, rep'⟩ := admin_fire (r := kschema defs .call) (vals := [encE a, encK K]) (k := 2)
        (s' := .ev a (.arg :: K))
        solved image oIn (Multiset.mem_cons_self _ _) reads rfl rfl rfl rfl (by decide) (by decide)
        (by decide) rfl rfl
      rw [Multiset.erase_cons_head] at rep'
      exact ⟨_, Translated.fire (schema := kschema defs) KRule.call [o] [] valid, rep'⟩
  | left v b K F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      obtain ⟨valid, rep'⟩ := admin_fire (r := kschema defs .left) (vals := [v, encE b, encK K]) (k := 3)
        (s' := .ev b (.right v :: K))
        solved image oIn (Multiset.mem_cons_self _ _) reads rfl rfl rfl rfl (by decide) (by decide)
        (by decide) rfl rfl
      rw [Multiset.erase_cons_head] at rep'
      exact ⟨_, Translated.fire (schema := kschema defs) KRule.left [o] [] valid, rep'⟩
  | right v w K F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      obtain ⟨valid, rep'⟩ := admin_fire (r := kschema defs .right) (vals := [v, w, encK K]) (k := 3)
        (s' := .ret (node v w) K)
        solved image oIn (Multiset.mem_cons_self _ _) reads rfl rfl rfl rfl (by decide) (by decide)
        (by decide) rfl rfl
      rw [Multiset.erase_cons_head] at rep'
      exact ⟨_, Translated.fire (schema := kschema defs) KRule.right [o] [] valid, rep'⟩
  | arg w K F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      obtain ⟨valid, rep'⟩ := admin_fire (r := kschema defs .arg) (vals := [w, encK K]) (k := 2)
        (s' := .ap w K)
        solved image oIn (Multiset.mem_cons_self _ _) reads rfl rfl rfl rfl (by decide) (by decide)
        (by decide) rfl rfl
      rw [Multiset.erase_cons_head] at rep'
      exact ⟨_, Translated.fire (schema := kschema defs) KRule.arg [o] [] valid, rep'⟩
  | apply u j w K F n θ mgu =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      have erased : (C.present.erase o).val.map (readAt μ) = (SRow.version u ::ₘ F).map SRow.enc := by
        rw [erase_image image oIn (Multiset.mem_cons_self _ _) reads, Multiset.erase_cons_head]
      obtain ⟨o', o'In, reads'⟩ := pick_source erased (Multiset.mem_cons_self _ _)
      obtain ⟨valid, rep'⟩ := apply_fire solved image oIn (Finset.mem_of_mem_erase o'In)
        (fun h => by rw [← h] at o'In; exact Finset.notMem_erase o _ o'In) rfl reads reads' mgu
      exact ⟨_, Translated.fire (schema := kschema defs) (KRule.apply u j) [o] [o'] valid, rep'⟩
  | redefine u u' F n =>
      obtain ⟨o, oIn, reads⟩ := head rfl
      have erased : (C.present.erase o).val.map (readAt μ) = (SRow.version u ::ₘ F).map SRow.enc := by
        rw [erase_image image oIn (Multiset.mem_cons_self _ _) reads, Multiset.erase_cons_head]
      obtain ⟨o', o'In, reads'⟩ := pick_source erased (Multiset.mem_cons_self _ _)
      obtain ⟨valid, rep'⟩ := redefine_fire (defs := defs) solved image oIn
        (Finset.mem_of_mem_erase o'In)
        (fun h => by rw [← h] at o'In; exact Finset.notMem_erase o _ o'In) rfl reads reads'
      exact ⟨_, Translated.fire (schema := kschema defs) (KRule.redefine u u') [o, o'] [] valid,
        rep'⟩

/-! ## Completeness -/

/-- **An administrative firing is a machine step**, given the shapes its pattern forces. -/
theorem admin_complete {defs : Defs} {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {i : KRule defs} {p q : Pat} (take : (kschema defs i).take = [p])
    (read : (kschema defs i).read = []) (make : (kschema defs i).make = [q])
    {taken readOccs : List Occ} (valid : ((kschema defs i).firing n taken readOccs).Valid A Occ.label C)
    {k : ℕ} (covers : ∀ x < k, x ∈ p.vars) (within : ∀ x ∈ p.vars, x < k)
    (withinq : ∀ x ∈ q.vars, x < k)
    (shape : ∀ s ∈ Ws, (∃ σ : Subst rows, σ.applyTerm (p.at n) = σ.applyTerm s.enc) →
      ∃ vals : List Tm, vals.length = k ∧ Pat.fill vals p = s.enc ∧ ∃ s', Pat.fill vals q = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1)) :
    ∃ Ws', KStep defs (Ws, n) (Ws', n + 1) ∧
      ORepresents (((kschema defs i).firing n taken readOccs).result Occ.label C) (Ws'.map SRow.enc)
        (n + 1) := by
  obtain ⟨-, takenIn, -, -, takeLength, readLength⟩ := valid_shape valid
  obtain ⟨o, rfl⟩ : ∃ o, taken = [o] := List.length_eq_one_iff.mp (by rw [← takeLength, take]; rfl)
  have readNil : readOccs = [] := List.length_eq_zero_iff.mp (by rw [← readLength, read]; rfl)
  subst readNil
  have oIn := takenIn o (List.mem_singleton_self o)
  obtain ⟨σ, unifies⟩ := valid_unifiable solved valid
  obtain ⟨s, sIn, reads⟩ := read_source image oIn
  have unif : σ.applyTerm (p.at n) = σ.applyTerm s.enc := by
    have member : (p.at n, readAt μ o) ∈ schemaProblem (kschema defs i) n μ [o] [] := by
      unfold schemaProblem problem
      rw [take, read]
      simp
    have := unifies _ member
    rwa [reads] at this
  obtain ⟨vals, length, source, s', target, step⟩ := shape s sIn ⟨σ, unif⟩
  obtain ⟨-, rep'⟩ := admin_fire solved image oIn sIn reads take read make length covers within
    withinq source target
  refine ⟨s' ::ₘ Ws.erase s, ?_, rep'⟩
  have := step (Ws.erase s)
  rwa [Multiset.cons_erase sIn] at this

theorem shape_val {defs : Defs} {n : ℕ} {s : SRow} (good : s.Good)
    (h : ∃ σ : Subst rows, σ.applyTerm ((pev (pval (.var 0)) (.var 1)).at n) = σ.applyTerm s.enc) :
    ∃ vals : List Tm, vals.length = 2 ∧ Pat.fill vals (pev (pval (.var 0)) (.var 1)) = s.enc ∧
      ∃ s', Pat.fill vals (pret (.var 0) (.var 1)) = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1) := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨tag, body⟩ := tag_forced (k := 120) h
  obtain ⟨e, K, rfl⟩ := good_ev good tag
  obtain ⟨one, -⟩ := node_forced body
  rcases ex_forced (k := 130) one with ⟨-, t, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨[t, encK K], rfl, rfl, .ret t K, rfl, fun F => .val t K F n⟩
  · omega
  · omega

theorem shape_pair {defs : Defs} {n : ℕ} {s : SRow} (good : s.Good)
    (h : ∃ σ : Subst rows,
      σ.applyTerm ((pev (ppair (.var 0) (.var 1)) (.var 2)).at n) = σ.applyTerm s.enc) :
    ∃ vals : List Tm, vals.length = 3 ∧ Pat.fill vals (pev (ppair (.var 0) (.var 1)) (.var 2)) = s.enc ∧
      ∃ s', Pat.fill vals (pev (.var 0) (pleft (.var 1) (.var 2))) = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1) := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨tag, body⟩ := tag_forced (k := 120) h
  obtain ⟨e, K, rfl⟩ := good_ev good tag
  obtain ⟨one, -⟩ := node_forced body
  rcases ex_forced (k := 131) one with ⟨h, -⟩ | ⟨-, a, b, rfl, -⟩ | ⟨h, -⟩
  · omega
  · exact ⟨[encE a, encE b, encK K], rfl, rfl, .ev a (.left b :: K), rfl, fun F => .pair a b K F n⟩
  · omega

theorem shape_call {defs : Defs} {n : ℕ} {s : SRow} (good : s.Good)
    (h : ∃ σ : Subst rows, σ.applyTerm ((pev (pcall (.var 0)) (.var 1)).at n) = σ.applyTerm s.enc) :
    ∃ vals : List Tm, vals.length = 2 ∧ Pat.fill vals (pev (pcall (.var 0)) (.var 1)) = s.enc ∧
      ∃ s', Pat.fill vals (pev (.var 0) (parg (.var 1))) = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1) := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨tag, body⟩ := tag_forced (k := 120) h
  obtain ⟨e, K, rfl⟩ := good_ev good tag
  obtain ⟨one, -⟩ := node_forced body
  rcases ex_forced (k := 132) one with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, a, rfl, -⟩
  · omega
  · omega
  · exact ⟨[encE a, encK K], rfl, rfl, .ev a (.arg :: K), rfl, fun F => .call a K F n⟩

theorem shape_left {defs : Defs} {n : ℕ} {s : SRow} (good : s.Good)
    (h : ∃ σ : Subst rows,
      σ.applyTerm ((pret (.var 0) (pleft (.var 1) (.var 2))).at n) = σ.applyTerm s.enc) :
    ∃ vals : List Tm, vals.length = 3 ∧ Pat.fill vals (pret (.var 0) (pleft (.var 1) (.var 2))) = s.enc ∧
      ∃ s', Pat.fill vals (pev (.var 1) (pright (.var 0) (.var 2))) = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1) := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨tag, body⟩ := tag_forced (k := 121) h
  obtain ⟨v, K, rfl⟩ := good_ret good tag
  obtain ⟨-, two⟩ := node_forced body
  rcases frame_forced (k := 140) two with ⟨-, b, K', rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨[v, encE b, encK K'], rfl, rfl, .ev b (.right v :: K'), rfl, fun F => .left v b K' F n⟩
  · omega
  · omega

theorem shape_right {defs : Defs} {n : ℕ} {s : SRow} (good : s.Good)
    (h : ∃ σ : Subst rows,
      σ.applyTerm ((pret (.var 1) (pright (.var 0) (.var 2))).at n) = σ.applyTerm s.enc) :
    ∃ vals : List Tm, vals.length = 3 ∧ Pat.fill vals (pret (.var 1) (pright (.var 0) (.var 2))) = s.enc ∧
      ∃ s', Pat.fill vals (pret (.cell (.var 0) (.var 1)) (.var 2)) = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1) := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨tag, body⟩ := tag_forced (k := 121) h
  obtain ⟨w, K, rfl⟩ := good_ret good tag
  obtain ⟨-, two⟩ := node_forced body
  rcases frame_forced (k := 141) two with ⟨h, -⟩ | ⟨-, v, K', rfl⟩ | ⟨h, -⟩
  · omega
  · exact ⟨[v, w, encK K'], rfl, rfl, .ret (node v w) K', rfl, fun F => .right v w K' F n⟩
  · omega

theorem shape_arg {defs : Defs} {n : ℕ} {s : SRow} (good : s.Good)
    (h : ∃ σ : Subst rows, σ.applyTerm ((pret (.var 0) (parg (.var 1))).at n) = σ.applyTerm s.enc) :
    ∃ vals : List Tm, vals.length = 2 ∧ Pat.fill vals (pret (.var 0) (parg (.var 1))) = s.enc ∧
      ∃ s', Pat.fill vals (pap (.var 0) (.var 1)) = s'.enc ∧
        ∀ F, KStep defs (s ::ₘ F, n) (s' ::ₘ F, n + 1) := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨tag, body⟩ := tag_forced (k := 121) h
  obtain ⟨w, K, rfl⟩ := good_ret good tag
  obtain ⟨-, two⟩ := node_forced body
  rcases frame_forced (k := 142) two with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, K', rfl⟩
  · omega
  · omega
  · exact ⟨[w, encK K'], rfl, rfl, .ap w K', rfl, fun F => .arg w K' F n⟩

/-- **An admitted equation firing is a machine step answering a call.** -/
theorem apply_complete {defs : Defs} {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    (good : ∀ s ∈ Ws, s.Good) {u : ℕ} {j : Fin (defs u).length} {taken readOccs : List Occ}
    (valid : ((kschema defs (.apply u j)).firing n taken readOccs).Valid A Occ.label C) :
    ∃ Ws', KStep defs (Ws, n) (Ws', n + 1) ∧
      ORepresents (((kschema defs (.apply u j)).firing n taken readOccs).result Occ.label C)
        (Ws'.map SRow.enc) (n + 1) := by
  obtain ⟨-, takenIn, readIn, apart, takeLength, readLength⟩ := valid_shape valid
  obtain ⟨o, rfl⟩ : ∃ o, taken = [o] := List.length_eq_one_iff.mp (by rw [← takeLength]; rfl)
  obtain ⟨o', rfl⟩ : ∃ o', readOccs = [o'] := List.length_eq_one_iff.mp (by rw [← readLength]; rfl)
  have oIn := takenIn o (List.mem_singleton_self o)
  have o'In := readIn o' (List.mem_singleton_self o')
  have ne : o ≠ o' := fun h => apart o (List.mem_singleton_self o) (h ▸ List.mem_singleton_self o')
  obtain ⟨σ, unifies⟩ := valid_unifiable solved valid
  obtain ⟨s, sIn, reads⟩ := read_source image oIn
  have erased := erase_image image oIn sIn reads
  obtain ⟨s₂, s₂In, reads'⟩ := read_source erased (Finset.mem_erase.mpr ⟨fun h => ne h.symm, o'In⟩)
  have first : σ.applyTerm ((pap ((defs u).get j).lhs (.var (kname ((defs u).get j)))).at n) =
      σ.applyTerm s.enc := by
    have := unifies _ (show ((pap ((defs u).get j).lhs (.var (kname ((defs u).get j)))).at n,
      readAt μ o) ∈ schemaProblem (kschema defs (.apply u j)) n μ [o] [o'] by
        simp [schemaProblem, problem, kschema])
    rwa [reads] at this
  have second : σ.applyTerm ((ptag 41 (.sym u)).at n) = σ.applyTerm s₂.enc := by
    have := unifies _ (show ((ptag 41 (.sym u)).at n, readAt μ o') ∈
      schemaProblem (kschema defs (.apply u j)) n μ [o] [o'] by
        simp [schemaProblem, problem, kschema])
    rwa [reads'] at this
  obtain ⟨tag, body⟩ := tag_forced (k := 122) first
  obtain ⟨w, K, rfl⟩ := good_ap (good s sIn) tag
  obtain ⟨callUnif, -⟩ := node_forced body
  obtain ⟨tag₂, body₂⟩ := tag_forced (k := 41) second
  obtain ⟨u₂, rfl⟩ := good_version (good s₂ (Multiset.mem_of_mem_erase s₂In)) tag₂
  have uu : u = u₂ := const_forced body₂
  subst uu
  obtain ⟨θ, mgu⟩ := exists_isMGU ⟨σ, (unifies_single_iff σ _ _).mpr callUnif⟩
  have shape : Ws = .ap w K ::ₘ .version u ::ₘ (Ws.erase (.ap w K)).erase (.version u) := by
    rw [Multiset.cons_erase s₂In, Multiset.cons_erase sIn]
  obtain ⟨-, rep'⟩ := apply_fire (j := j) solved image oIn o'In ne shape reads reads' mgu
  refine ⟨_, ?_, rep'⟩
  have step := KStep.apply (defs := defs) u j w K ((Ws.erase (.ap w K)).erase (.version u)) n θ mgu
  rw [← shape] at step
  exact step

/-- **An admitted redefinition firing is a machine redefinition.** -/
theorem redefine_complete {defs : Defs} {C : Config} {n : ℕ} {μ : Subst rows}
    (solved : SolvedForm C n μ) {Ws : Multiset SRow}
    (image : C.present.val.map (readAt μ) = Ws.map SRow.enc) (good : ∀ s ∈ Ws, s.Good) {u u' : ℕ}
    {taken readOccs : List Occ}
    (valid : ((kschema defs (.redefine u u')).firing n taken readOccs).Valid A Occ.label C) :
    ∃ Ws', KStep defs (Ws, n) (Ws', n + 1) ∧
      ORepresents (((kschema defs (.redefine u u')).firing n taken readOccs).result Occ.label C)
        (Ws'.map SRow.enc) (n + 1) := by
  obtain ⟨nodup, takenIn, -, -, takeLength, readLength⟩ := valid_shape valid
  obtain ⟨o, o', rfl⟩ : ∃ o o', taken = [o, o'] := List.length_eq_two.mp (by rw [← takeLength]; rfl)
  have readNil : readOccs = [] := List.length_eq_zero_iff.mp (by rw [← readLength]; rfl)
  subst readNil
  have oIn := takenIn o List.mem_cons_self
  have o'In := takenIn o' (List.mem_cons_of_mem _ (List.mem_singleton_self o'))
  have ne : o ≠ o' := fun h => (List.nodup_cons.mp nodup).1 (h ▸ List.mem_singleton_self o')
  obtain ⟨σ, unifies⟩ := valid_unifiable solved valid
  obtain ⟨s, sIn, reads⟩ := read_source image oIn
  have erased := erase_image image oIn sIn reads
  obtain ⟨s₂, s₂In, reads'⟩ := read_source erased (Finset.mem_erase.mpr ⟨fun h => ne h.symm, o'In⟩)
  have first : σ.applyTerm ((ptag 123 (.sym u')).at n) = σ.applyTerm s.enc := by
    have := unifies _ (show ((ptag 123 (.sym u')).at n, readAt μ o) ∈
      schemaProblem (kschema defs (.redefine u u')) n μ [o, o'] [] by
        simp [schemaProblem, problem, kschema])
    rwa [reads] at this
  have second : σ.applyTerm ((ptag 41 (.sym u)).at n) = σ.applyTerm s₂.enc := by
    have := unifies _ (show ((ptag 41 (.sym u)).at n, readAt μ o') ∈
      schemaProblem (kschema defs (.redefine u u')) n μ [o, o'] [] by
        simp [schemaProblem, problem, kschema])
    rwa [reads'] at this
  obtain ⟨tag, body⟩ := tag_forced (k := 123) first
  obtain ⟨u₁, rfl⟩ := good_redef (good s sIn) tag
  have uu' : u' = u₁ := const_forced body
  subst uu'
  obtain ⟨tag₂, body₂⟩ := tag_forced (k := 41) second
  obtain ⟨u₂, rfl⟩ := good_version (good s₂ (Multiset.mem_of_mem_erase s₂In)) tag₂
  have uu : u = u₂ := const_forced body₂
  subst uu
  have shape : Ws = .redef u' ::ₘ .version u ::ₘ (Ws.erase (.redef u')).erase (.version u) := by
    rw [Multiset.cons_erase s₂In, Multiset.cons_erase sIn]
  obtain ⟨-, rep'⟩ := redefine_fire (defs := defs) solved image oIn o'In ne shape reads reads'
  refine ⟨_, ?_, rep'⟩
  have step := KStep.redefine (defs := defs) u u' ((Ws.erase (.redef u')).erase (.version u)) n
  rw [← shape] at step
  exact step

/-- **Completeness**: every admitted translated firing from represented well-formed rows is the
image of one machine step, and its result represents that step's result. -/
theorem nested_complete {defs : Defs} {C : Config} {Ws : Multiset SRow} {n : ℕ}
    (rep : ORepresents C (Ws.map SRow.enc) n) (good : ∀ s ∈ Ws, s.Good) {q : Config × ℕ}
    (firing : Translated (kschema defs) (C, n) q) :
    ∃ Ws', KStep defs (Ws, n) (Ws', q.2) ∧ ORepresents q.1 (Ws'.map SRow.enc) q.2 := by
  obtain ⟨μ, solved, image⟩ := rep
  cases firing with
  | fire i taken read valid =>
      cases i with
      | val =>
          exact admin_complete (k := 2) solved image rfl rfl rfl valid (by decide) (by decide)
            (by decide) fun s sIn h => shape_val (good s sIn) h
      | pair =>
          exact admin_complete (k := 3) solved image rfl rfl rfl valid (by decide) (by decide)
            (by decide) fun s sIn h => shape_pair (good s sIn) h
      | call =>
          exact admin_complete (k := 2) solved image rfl rfl rfl valid (by decide) (by decide)
            (by decide) fun s sIn h => shape_call (good s sIn) h
      | left =>
          exact admin_complete (k := 3) solved image rfl rfl rfl valid (by decide) (by decide)
            (by decide) fun s sIn h => shape_left (good s sIn) h
      | right =>
          exact admin_complete (k := 3) solved image rfl rfl rfl valid (by decide) (by decide)
            (by decide) fun s sIn h => shape_right (good s sIn) h
      | arg =>
          exact admin_complete (k := 2) solved image rfl rfl rfl valid (by decide) (by decide)
            (by decide) fun s sIn h => shape_arg (good s sIn) h
      | apply u j => exact apply_complete solved image good valid
      | redefine u u' => exact redefine_complete solved image good valid

/-! ## Runs -/

theorem kstep_good {defs : Defs} {s s' : Multiset SRow × ℕ} (step : KStep defs s s')
    (good : ∀ r ∈ s.1, r.Good) : ∀ r ∈ s'.1, r.Good := by
  cases step with
  | val t K F n | pair a b K F n | call a K F n | left v b K F n | right v w K F n | arg w K F n =>
      intro r member
      rcases Multiset.mem_cons.mp member with rfl | member
      · trivial
      · exact good r (Multiset.mem_cons_of_mem member)
  | apply u j w K F n θ mgu =>
      intro r member
      simp only [Multiset.mem_cons] at member
      rcases member with rfl | rfl | rfl | member
      · trivial
      · trivial
      · trivial
      · obtain ⟨r₀, r₀In, rfl⟩ := Multiset.mem_map.mp member
        exact (good r₀ (by simp [r₀In])).subst θ
  | redefine u u' F n =>
      intro r member
      simp only [Multiset.mem_cons] at member
      rcases member with rfl | rfl | member
      · trivial
      · trivial
      · exact good r (by simp [member])

theorem nested_runs_sound {defs : Defs} {s s' : Multiset SRow × ℕ}
    (run : Relation.ReflTransGen (KStep defs) s s') {C : Config} (rep : ORepresents C (s.1.map SRow.enc) s.2) :
    ∃ D, Relation.ReflTransGen (Translated (kschema defs)) (C, s.2) (D, s'.2) ∧
      ORepresents D (s'.1.map SRow.enc) s'.2 := by
  induction run with
  | refl => exact ⟨C, .refl, rep⟩
  | @tail b c _ step ih =>
      obtain ⟨D, path, rep'⟩ := ih
      obtain ⟨W, m⟩ := b
      obtain ⟨E, firing, rep''⟩ := nested_sound rep' step
      exact ⟨E, path.tail firing, rep''⟩

theorem nested_runs_complete {defs : Defs} {p q : Config × ℕ}
    (run : Relation.ReflTransGen (Translated (kschema defs)) p q) {Ws : Multiset SRow}
    (rep : ORepresents p.1 (Ws.map SRow.enc) p.2) (good : ∀ s ∈ Ws, s.Good) :
    ∃ Ws', Relation.ReflTransGen (KStep defs) (Ws, p.2) (Ws', q.2) ∧
      ORepresents q.1 (Ws'.map SRow.enc) q.2 ∧ ∀ s ∈ Ws', s.Good := by
  induction run with
  | refl => exact ⟨Ws, .refl, rep, good⟩
  | @tail b c _ firing ih =>
      obtain ⟨Ws', path, rep', good'⟩ := ih
      obtain ⟨D, m⟩ := b
      obtain ⟨Ws'', step, rep''⟩ := nested_complete rep' good' firing
      exact ⟨Ws'', path.tail step, rep'', kstep_good step good'⟩

/-- **Adequacy of nested calls on the ordinary step.** From well-formed source rows whose terms
name only scope `0`, every machine run is matched by a run of translated firings to a
configuration representing its end, and every run of translated firings ends in a configuration
representing the end of a machine run. -/
theorem nested_execution (defs : Defs) (l : List SRow) (good : ∀ s ∈ l, s.Good)
    (bounded : ∀ s ∈ l, Bounded 1 s.enc) (Ws : Multiset SRow) (m : ℕ) :
    (Relation.ReflTransGen (KStep defs) ((l : Multiset SRow), 1) (Ws, m) →
      ∃ D, Relation.ReflTransGen (Translated (kschema defs)) (openInitial (l.map SRow.enc), 1) (D, m) ∧
        ORepresents D (Ws.map SRow.enc) m) ∧
    (∀ D, Relation.ReflTransGen (Translated (kschema defs)) (openInitial (l.map SRow.enc), 1) (D, m) →
      ∃ Ws', Relation.ReflTransGen (KStep defs) ((l : Multiset SRow), 1) (Ws', m) ∧
        ORepresents D (Ws'.map SRow.enc) m) := by
  have rep : ORepresents (openInitial (l.map SRow.enc)) (((l : Multiset SRow)).map SRow.enc) 1 := by
    rw [Multiset.map_coe]
    exact openInitial_represents _ fun t member => by
      obtain ⟨s, sIn, rfl⟩ := List.mem_map.mp member
      exact bounded s sIn
  refine ⟨fun run => nested_runs_sound run rep, fun D run => ?_⟩
  obtain ⟨Ws', path, rep', -⟩ := nested_runs_complete run rep fun s member => good s member
  exact ⟨Ws', path, rep'⟩

/-- **Translated runs are reference runs in evaluation contexts.** Every run of translated firings
from the initial configuration ends in a configuration representing a machine configuration whose
unloading is reached by the reference semantics. -/
theorem translated_is_reference (defs : Defs) (l : List SRow) (good : ∀ s ∈ l, s.Good)
    (bounded : ∀ s ∈ l, Bounded 1 s.enc) (D : Config) (m : ℕ)
    (run : Relation.ReflTransGen (Translated (kschema defs)) (openInitial (l.map SRow.enc), 1) (D, m)) :
    ∃ Ws', ORepresents D (Ws'.map SRow.enc) m ∧ ∃ m', m' ≤ m ∧
      Relation.ReflTransGen (CStep defs) (unloadAll (l : Multiset SRow), 1) (unloadAll Ws', m') := by
  obtain ⟨Ws', path, rep⟩ := (nested_execution defs l good bounded 0 m).2 D run
  obtain ⟨m', le, reference⟩ := kruns_unload path (le_refl 1)
  exact ⟨Ws', rep, m', le, reference⟩

#print axioms matcher_isMGU
#print axioms isMGU_extend
#print axioms admin_fire
#print axioms apply_mgu
#print axioms apply_fire
#print axioms redefine_fire
#print axioms nested_sound
#print axioms admin_complete
#print axioms apply_complete
#print axioms redefine_complete
#print axioms nested_complete
#print axioms kstep_good
#print axioms nested_runs_sound
#print axioms nested_runs_complete
#print axioms nested_execution
#print axioms translated_is_reference

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
