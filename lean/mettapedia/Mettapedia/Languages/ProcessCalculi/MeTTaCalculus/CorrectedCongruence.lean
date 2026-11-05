import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedAdequacy

/-!
# The corrected step modulo the bag laws

The manuscript's structural equivalence contains the monoid laws of parallel
composition. Here the relational semantics takes as its equivalence `BagEq`:
equal closed top-level components, up to order. It contains alpha-equivalence
and the commutativity, associativity and unit laws. The executable `cstepBag`
runs COMM on any ordered pair of guards among the components and REFL on any
reflected component. It is sound for the manuscript's rules with this
equivalence, and complete on the closing fragment up to `BagEq`.

The laws act on the parallel composition being executed, not inside patterns:
a pattern compared modulo commutativity would need unification modulo
associativity and commutativity, which has no principal unifier in general.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm (psubst pvars)

/-! ## Choosing components -/

/-- Every way to pick one element of a list, with the others in order. -/
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: l => (a, l) :: (picks l).map fun choice => (choice.1, a :: choice.2)

theorem perm_of_mem_picks {α : Type} : ∀ {l : List α} {a : α} {rest : List α},
    (a, rest) ∈ picks l → l.Perm (a :: rest)
  | [], _, _, h => by simp [picks] at h
  | b :: l, a, rest, h => by
      simp only [picks, List.mem_cons, List.mem_map, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨⟨c, r⟩, member, rfl, rfl⟩
      · exact List.Perm.refl _
      · exact ((perm_of_mem_picks member).cons b).trans (List.Perm.swap c b r)

theorem mem_picks_of_perm {α : Type} [DecidableEq α] : ∀ {l : List α} {a : α} {rest : List α},
    l.Perm (a :: rest) → ∃ rest', (a, rest') ∈ picks l ∧ rest'.Perm rest
  | [], _, _, h => absurd h.length_eq (by simp)
  | b :: l, a, rest, h => by
      by_cases same : a = b
      · subst same
        exact ⟨l, by simp [picks], h.cons_inv⟩
      · have bIn : b ∈ rest := by
          have : b ∈ a :: rest := h.subset (List.mem_cons_self ..)
          rcases List.mem_cons.mp this with eq | inRest
          · exact absurd eq.symm same
          · exact inRest
        have split : rest.Perm (b :: rest.erase b) := List.perm_cons_erase bIn
        have moved : (b :: l).Perm (b :: a :: rest.erase b) :=
          h.trans ((split.cons a).trans (List.Perm.swap b a _))
        obtain ⟨r', member, perm⟩ := mem_picks_of_perm moved.cons_inv
        refine ⟨b :: r', ?_, (perm.cons b).trans split.symm⟩
        simp only [picks, List.mem_cons, List.mem_map, Prod.mk.injEq]
        exact .inr ⟨(a, r'), member, rfl, rfl⟩

theorem mem_picks_append {α : Type} : ∀ {l₁ : List α} (l₂ : List α) {a : α} {rest : List α},
    (a, rest) ∈ picks l₁ → (a, rest ++ l₂) ∈ picks (l₁ ++ l₂)
  | [], _, _, _, h => by simp [picks] at h
  | b :: l, l₂, a, rest, h => by
      simp only [picks, List.mem_cons, List.mem_map, Prod.mk.injEq] at h
      simp only [List.cons_append, picks, List.mem_cons, List.mem_map, Prod.mk.injEq]
      rcases h with ⟨rfl, rfl⟩ | ⟨⟨c, r⟩, member, rfl, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨(c, r ++ l₂), mem_picks_append l₂ member, rfl, rfl⟩

/-- Lifting a choice through a map. -/
theorem perm_map_cons_lift {α β : Type} [DecidableEq α] (f : α → β) {l : List α} {b : β} {m : List β}
    (h : (l.map f).Perm (b :: m)) : ∃ a l', l.Perm (a :: l') ∧ f a = b ∧ (l'.map f).Perm m := by
  have bIn : b ∈ l.map f := h.symm.subset (List.mem_cons_self ..)
  obtain ⟨a, aIn, rfl⟩ := List.mem_map.mp bIn
  have split : l.Perm (a :: l.erase a) := List.perm_cons_erase aIn
  refine ⟨a, l.erase a, split, rfl, ?_⟩
  have mapped : (l.map f).Perm (f a :: (l.erase a).map f) := by simpa using split.map f
  exact (h.symm.trans mapped).cons_inv.symm

/-! ## Components of closed processes -/

mutual
/-- Number of constructors. -/
def psize : Pattern → ℕ
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply _ args => psizeList args + 1
  | .lambda _ body => psize body + 1
  | .multiLambda _ _ body => psize body + 1
  | .subst body repl => psize body + psize repl + 1
  | .collection _ elems _ => psizeList elems + 1
def psizeList : List Pattern → ℕ
  | [] => 0
  | p :: ps => psize p + psizeList ps
end

theorem psize_le_list {p : Pattern} {ps : List Pattern} (member : p ∈ ps) : psize p ≤ psizeList ps := by
  induction ps with
  | nil => cases member
  | cons q qs ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp [psizeList]
      · have := ih later; simp only [psizeList]; omega

theorem componentsList_eq_flatMap (ps : List Pattern) : componentsList ps = ps.flatMap components := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [componentsList, ih]

/-- A component is not larger than its process. -/
theorem psize_le_of_mem_components (p : Pattern) : ∀ c ∈ components p, psize c ≤ psize p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ c ∈ components q, psize c ≤ psize q) with
  | collection ct elems rest ih =>
      intro c member
      by_cases bag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := bag
        simp only [components, componentsList_eq_flatMap, List.mem_flatMap] at member
        obtain ⟨q, inside, inQ⟩ := member
        have := ih q inside c inQ
        have := psize_le_list inside
        simp only [psize]; omega
      · have : components (.collection ct elems rest) = [.collection ct elems rest] := by
          rcases ct <;> rcases rest <;> simp_all [components]
        rw [this, List.mem_singleton] at member
        subst member; exact le_rfl
  | apply c args ih =>
      intro d member
      by_cases zero : c = "MZero" ∧ args = []
      · obtain ⟨rfl, rfl⟩ := zero; simp [components] at member
      · have : components (.apply c args) = [.apply c args] := by
          unfold components; split <;> simp_all
        rw [this, List.mem_singleton] at member
        subst member; exact le_rfl
  | bvar n => intro c member; simp [components] at member; subst member; exact le_rfl
  | fvar x => intro c member; simp [components] at member; subst member; exact le_rfl
  | lambda nm body ih => intro c member; simp [components] at member; subst member; exact le_rfl
  | multiLambda n nms body ih => intro c member; simp [components] at member; subst member; exact le_rfl
  | subst body repl ihb ihr => intro c member; simp [components] at member; subst member; exact le_rfl
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member c inC
      rcases List.mem_cons.mp member with rfl | later
      · exact head c inC
      · exact tail q later c inC

/-- Closing commutes with taking components: bags and `0` are not binders. -/
theorem components_closeIn (p : Pattern) : ∀ env : List (List String),
    components (closeIn env p) = (components p).map (closeIn env) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ env : List (List String),
      components (closeIn env q) = (components q).map (closeIn env)) with
  | collection ct elems rest ih =>
      intro env
      by_cases bag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := bag
        simp only [closeIn, closeList_eq_map, components, componentsList_eq_flatMap, List.flatMap_map,
          List.map_flatMap]
        exact List.flatMap_congr fun q member => ih q member env
      · have plain : components (.collection ct elems rest) = [.collection ct elems rest] := by
          rcases ct <;> rcases rest <;> simp_all [components]
        have plainClosed : components (closeIn env (.collection ct elems rest)) =
            [closeIn env (.collection ct elems rest)] := by
          simp only [closeIn, closeList_eq_map]
          rcases ct <;> rcases rest <;> simp_all [components]
        rw [plain, plainClosed]; rfl
  | apply c args ih =>
      intro env
      by_cases zero : c = "MZero" ∧ args = []
      · obtain ⟨rfl, rfl⟩ := zero; simp [components, closeIn, closeList]
      · have plain : components (.apply c args) = [.apply c args] := by
          unfold components; split <;> simp_all
        have plainClosed : components (closeIn env (.apply c args)) = [closeIn env (.apply c args)] := by
          rw [closeIn_apply]
          unfold components
          split
          · rename_i heq; simp at heq
          · rename_i heq
            simp only [Pattern.apply.injEq] at heq
            obtain ⟨rfl, list⟩ := heq
            have argsNil : args = [] := by
              rw [if_neg (show ¬ ("MZero" : String) = "MFor" from by decide)] at list
              exact List.map_eq_nil_iff.mp list
            exact absurd ⟨rfl, argsNil⟩ zero
          · rfl
        rw [plain, plainClosed]; rfl
  | fvar x => intro env; cases h : lookupBound env x <;> simp [closeIn, h, components, boundCode]
  | bvar n => intro env; simp [closeIn, components]
  | lambda nm body ih => intro env; simp [closeIn, components]
  | multiLambda n nms body ih => intro env; simp [closeIn, components]
  | subst body repl ihb ihr => intro env; simp [closeIn, components]
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env
      rcases List.mem_cons.mp member with rfl | later
      · exact head env
      · exact tail q later env

/-- Components are leaves. -/
theorem components_of_mem_components (p : Pattern) : ∀ c ∈ components p, components c = [c] := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ c ∈ components q, components c = [c]) with
  | collection ct elems rest ih =>
      intro c member
      by_cases bag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := bag
        simp only [components, componentsList_eq_flatMap, List.mem_flatMap] at member
        obtain ⟨q, inside, inQ⟩ := member
        exact ih q inside c inQ
      · have plain : components (.collection ct elems rest) = [.collection ct elems rest] := by
          rcases ct <;> rcases rest <;> simp_all [components]
        rw [plain, List.mem_singleton] at member
        subst member; exact plain
  | apply c args ih =>
      intro d member
      by_cases zero : c = "MZero" ∧ args = []
      · obtain ⟨rfl, rfl⟩ := zero; simp [components] at member
      · have plain : components (.apply c args) = [.apply c args] := by
          unfold components; split <;> simp_all
        rw [plain, List.mem_singleton] at member
        subst member; exact plain
  | bvar n => intro c member; simp [components] at member; subst member; simp [components]
  | fvar x => intro c member; simp [components] at member; subst member; simp [components]
  | lambda nm body ih => intro c member; simp [components] at member; subst member; simp [components]
  | multiLambda n nms body ih =>
      intro c member; simp [components] at member; subst member; simp [components]
  | subst body repl ihb ihr => intro c member; simp [components] at member; subst member; simp [components]
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member c inC
      rcases List.mem_cons.mp member with rfl | later
      · exact head c inC
      · exact tail q later c inC

/-! ## Equivalence modulo the bag laws -/

/-- Equal closed top-level components, up to order. -/
def BagEq (p q : Pattern) : Prop := (components (close p)).Perm (components (close q))

theorem BagEq.refl (p : Pattern) : BagEq p p := List.Perm.refl _
theorem BagEq.symm {p q : Pattern} (h : BagEq p q) : BagEq q p := List.Perm.symm h
theorem BagEq.trans {p q r : Pattern} (h : BagEq p q) (h' : BagEq q r) : BagEq p r := List.Perm.trans h h'

theorem BagEq.of_alphaEq {p q : Pattern} (h : AlphaEq p q) : BagEq p q := by
  unfold BagEq; rw [show close p = close q from h]

theorem bagEq_iff (p q : Pattern) :
    BagEq p q ↔ ((components p).map close).Perm ((components q).map close) := by
  unfold BagEq close; rw [components_closeIn, components_closeIn]

theorem BagEq.par_comm (p q : Pattern) : BagEq (par p q) (par q p) := by
  rw [bagEq_iff, components_par, components_par, List.map_append, List.map_append]
  exact List.perm_append_comm

theorem BagEq.par_assoc (p q r : Pattern) : BagEq (par (par p q) r) (par p (par q r)) := by
  rw [bagEq_iff, components_par_assoc]

theorem BagEq.par_zero (p : Pattern) : BagEq (par p pZero) p := by
  rw [bagEq_iff, components_par_zero]

theorem BagEq.par {p p' q q' : Pattern} (hp : BagEq p p') (hq : BagEq q q') : BagEq (par p q) (par p' q') := by
  rw [bagEq_iff] at *
  rw [components_par, components_par, List.map_append, List.map_append]
  exact hp.append hq

/-! ## The executable step modulo the bag laws -/

/-- One step of a closed process modulo the bag laws: COMM on any ordered pair
of guards among its components, and REFL on any reflected component. -/
def stepComps (avoid : List String) : ℕ → List Pattern → List Pattern
  | 0, _ => []
  | fuel + 1, cs =>
      (picks cs).flatMap fun choice =>
        ((picks choice.2).flatMap fun second =>
            (commClosed avoid choice.1 second.1).map fun r => pPar (r :: second.2)) ++
          (match choice.1 with
           | .apply "MRef" [x, a] =>
               (stepComps avoid fuel (components a)).map fun a' =>
                 pPar (pFor (tProc a') x pZero :: choice.2)
           | _ => [])

/-- **The corrected step modulo the bag laws.** -/
def cstepBag (p : Pattern) : List Pattern :=
  stepComps (pvars (close p)) (psize (close p) + 1) (components (close p))

/-- The manuscript's rules with the bag laws and alpha-equivalence as EQUIV. -/
inductive BagStep (admit : Admission) : Pattern → Pattern → Prop where
  | comm (t u x A B : Pattern) (bs : Bindings) (principal : Principal t u bs)
      (admitted : admit t A u B bs) :
      BagStep admit (par (pFor t x A) (pFor u x B)) (par (applyDot bs A) (applyDot bs B))
  | parallel {source target : Pattern} (surrounding : Pattern) :
      BagStep admit source target → BagStep admit (par source surrounding) (par target surrounding)
  | congruence {source source' target' target : Pattern} :
      BagEq source source' → BagStep admit source' target' → BagEq target' target →
      BagStep admit source target
  | reflect (x : Pattern) {source target : Pattern} :
      BagStep admit source target → BagStep admit (pReflect x source) (pFor (tProc target) x pZero)

/-- COMM at any position: the same rules without REFL. -/
inductive BagCommStep (admit : Admission) : Pattern → Pattern → Prop where
  | comm (t u x A B : Pattern) (bs : Bindings) (principal : Principal t u bs)
      (admitted : admit t A u B bs) :
      BagCommStep admit (par (pFor t x A) (pFor u x B)) (par (applyDot bs A) (applyDot bs B))
  | parallel {source target : Pattern} (surrounding : Pattern) :
      BagCommStep admit source target → BagCommStep admit (par source surrounding) (par target surrounding)
  | congruence {source source' target' target : Pattern} :
      BagEq source source' → BagCommStep admit source' target' → BagEq target' target →
      BagCommStep admit source target

theorem BagCommStep.toBagStep {admit : Admission} {p q : Pattern} (step : BagCommStep admit p q) :
    BagStep admit p q := by
  induction step with
  | comm t u x A B bs principal admitted => exact .comm t u x A B bs principal admitted
  | parallel surrounding _ ih => exact .parallel surrounding ih
  | congruence before _ after ih => exact .congruence before ih after

theorem Step.toBagStep {admit : Admission} {p q : Pattern} (step : Step admit p q) : BagStep admit p q := by
  induction step with
  | comm t u x A B bs principal admitted => exact .comm t u x A B bs principal admitted
  | parallel surrounding _ ih => exact .parallel surrounding ih
  | congruence before _ after ih => exact .congruence (.of_alphaEq before) ih (.of_alphaEq after)
  | reflect x _ ih => exact .reflect x ih

/-! ## Facts about components -/

theorem components_attr {P : Pattern} (property : Pattern → Prop)
    (bag : ∀ elems, property (.collection .hashBag elems none) → ∀ q ∈ elems, property q)
    (holds : property P) : ∀ c ∈ components P, property c := by
  induction P using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, property q → ∀ c ∈ components q, property c) with
  | collection ct elems rest ih =>
      intro c member
      by_cases isBag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := isBag
        simp only [components, componentsList_eq_flatMap, List.mem_flatMap] at member
        obtain ⟨q, inside, inQ⟩ := member
        exact ih q inside (bag elems holds q inside) c inQ
      · have plain : components (.collection ct elems rest) = [.collection ct elems rest] := by
          rcases ct <;> rcases rest <;> simp_all [components]
        rw [plain, List.mem_singleton] at member
        subst member; exact holds
  | apply c args ih =>
      intro d member
      by_cases zero : c = "MZero" ∧ args = []
      · obtain ⟨rfl, rfl⟩ := zero; simp [components] at member
      · have plain : components (.apply c args) = [.apply c args] := by
          unfold components; split <;> simp_all
        rw [plain, List.mem_singleton] at member
        subst member; exact holds
  | bvar n => intro c member; simp [components] at member; subst member; exact holds
  | fvar x => intro c member; simp [components] at member; subst member; exact holds
  | lambda nm body ih => intro c member; simp [components] at member; subst member; exact holds
  | multiLambda n nms body ih => intro c member; simp [components] at member; subst member; exact holds
  | subst body repl ihb ihr => intro c member; simp [components] at member; subst member; exact holds
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member holdsQ c inC
      rcases List.mem_cons.mp member with rfl | later
      · exact head holdsQ c inC
      · exact tail q later holdsQ c inC

theorem calcTerm_of_mem_components {P c : Pattern} (inCalc : calcTerm P = true) (member : c ∈ components P) :
    calcTerm c = true :=
  components_attr (fun p => calcTerm p = true) (fun elems h q inside => by
    simp only [calcTerm, Bool.and_eq_true, calcList_iff] at h; exact h.2 q inside) inCalc c member

theorem pvars_of_mem_components {P c : Pattern} (member : c ∈ components P) {z : String}
    (occurs : z ∈ pvars c) : z ∈ pvars P := by
  have := components_attr (P := P) (fun p => ∀ y ∈ pvars p, y ∈ pvars P)
    (fun elems h q inside y inQ => h y (mem_pvars_collection_of inside inQ)) (fun y h => h) c member
  exact this z occurs

theorem components_pPar_leaves (L : List Pattern) (leaves : ∀ c ∈ L, components c = [c]) :
    components (pPar L) = L := by
  simp only [pPar, components, componentsList_eq_flatMap]
  rw [List.flatMap_congr (g := fun c => [c]) leaves, List.flatMap_singleton']

theorem close_of_mem_closed_components {P c : Pattern} (member : c ∈ components (close P)) : close c = c := by
  unfold close at member
  rw [components_closeIn] at member
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp member
  exact close_close C

theorem leaf_of_mem_closed_components {P c : Pattern} (member : c ∈ components (close P)) :
    components c = [c] := components_of_mem_components _ c member

/-- What a step modulo the bag laws can be. -/
theorem mem_stepComps {avoid : List String} {fuel : ℕ} {cs : List Pattern} {Q : Pattern}
    (member : Q ∈ stepComps avoid (fuel + 1) cs) :
    ∃ c₁ rest₁, (c₁, rest₁) ∈ picks cs ∧
      ((∃ c₂ rest r, (c₂, rest) ∈ picks rest₁ ∧ r ∈ commClosed avoid c₁ c₂ ∧ Q = pPar (r :: rest)) ∨
        (∃ x a a', c₁ = pReflect x a ∧ a' ∈ stepComps avoid fuel (components a) ∧
          Q = pPar (pFor (tProc a') x pZero :: rest₁))) := by
  simp only [stepComps, List.mem_flatMap, List.mem_append] at member
  obtain ⟨⟨c₁, rest₁⟩, inPicks, inner⟩ := member
  refine ⟨c₁, rest₁, inPicks, ?_⟩
  rcases inner with ⟨⟨c₂, rest⟩, inSecond, inComm⟩ | inRefl
  · obtain ⟨r, rIn, rfl⟩ := List.mem_map.mp inComm
    exact .inl ⟨c₂, rest, r, inSecond, rIn, rfl⟩
  · simp only at inRefl
    split at inRefl
    · rename_i x a
      obtain ⟨a', a'In, rfl⟩ := List.mem_map.mp inRefl
      exact .inr ⟨x, a, a', rfl, a'In, rfl⟩
    · cases inRefl

/-! ## Soundness modulo the bag laws -/

theorem pvars_close_of_mem_components {P C : Pattern} (member : C ∈ components P) {z : String}
    (occurs : z ∈ pvars (close C)) : z ∈ pvars (close P) := by
  have closedMember : close C ∈ components (close P) := by
    unfold close; rw [components_closeIn]; exact List.mem_map_of_mem member
  exact pvars_of_mem_components closedMember occurs

theorem stepComps_sound (avoid : List String) : ∀ (fuel : ℕ) (P : Pattern), calcTerm P = true →
    (∀ z ∈ pvars (close P), z ∈ avoid) →
    ∀ Q ∈ stepComps avoid fuel (components (close P)), BagStep conventional P Q := by
  intro fuel
  induction fuel with
  | zero => intro P _ _ Q member; simp [stepComps] at member
  | succ fuel ih =>
      intro P inCalc fresh Q member
      have closedComps : components (close P) = (components P).map close := components_closeIn P []
      have leafAll : ∀ c ∈ components P, components c = [c] := components_of_mem_components P
      obtain ⟨c₁, rest₁, inPicks, which⟩ := mem_stepComps member
      have perm₁ := perm_of_mem_picks inPicks
      rw [closedComps] at perm₁
      obtain ⟨C₁, L₁, permC₁, closeC₁, permL₁⟩ := perm_map_cons_lift close perm₁
      have C₁mem : C₁ ∈ components P := permC₁.symm.subset (List.mem_cons_self ..)
      have restClosed : ∀ c ∈ rest₁, c ∈ components (close P) := fun c member =>
        (perm_of_mem_picks inPicks).symm.subset (List.mem_cons_of_mem _ member)
      rcases which with ⟨c₂, rest, r, inSecond, rIn, rfl⟩ | ⟨x, a, a', reflShape, a'In, rfl⟩
      · have perm₂ := perm_of_mem_picks inSecond
        obtain ⟨C₂, L, permC₂, closeC₂, permL⟩ := perm_map_cons_lift close (permL₁.trans perm₂)
        have C₂mem : C₂ ∈ components P :=
          permC₁.symm.subset (List.mem_cons_of_mem _ (permC₂.symm.subset (List.mem_cons_self ..)))
        have Lsub : ∀ c ∈ L, c ∈ components P := fun c member =>
          permC₁.symm.subset (List.mem_cons_of_mem _ (permC₂.symm.subset (List.mem_cons_of_mem _ member)))
        subst closeC₁ closeC₂
        cases g1 : asGuard (closeIn [] C₁) with
        | none => rw [show close C₁ = closeIn [] C₁ from rfl, commClosed_of_not_guard (.inl g1)] at rIn; cases rIn
        | some r1 =>
            cases g2 : asGuard (closeIn [] C₂) with
            | none =>
                rw [show close C₁ = closeIn [] C₁ from rfl, show close C₂ = closeIn [] C₂ from rfl,
                  commClosed_of_not_guard (.inr g2)] at rIn
                cases rIn
            | some r2 =>
                obtain ⟨t, xt, A, rfl, _⟩ := asGuard_closeIn g1
                obtain ⟨u, yu, B, rfl, _⟩ := asGuard_closeIn g2
                obtain ⟨calcT, _, calcA⟩ := calcTerm_pFor (calcTerm_of_mem_components inCalc C₁mem)
                obtain ⟨calcU, _, calcB⟩ := calcTerm_pFor (calcTerm_of_mem_components inCalc C₂mem)
                have freshPair : ∀ z ∈ pvars (close (par (pFor t xt A) (pFor u yu B))), z ∈ avoid := by
                  intro z occurs
                  unfold close at occurs
                  rw [closeIn_par, pvars_par] at occurs
                  rcases List.mem_append.mp occurs with h | h
                  · exact fresh z (pvars_close_of_mem_components C₁mem h)
                  · exact fresh z (pvars_close_of_mem_components C₂mem h)
                have sound := commClosed_sound avoid t xt A u yu B calcT calcU calcA calcB freshPair rIn
                have step₁ : BagStep conventional (par (par (pFor t xt A) (pFor u yu B)) (pPar L))
                    (par r (pPar L)) := .parallel _ (Step.toBagStep sound)
                have leavesL : ∀ c ∈ L, components c = [c] := fun c member => leafAll c (Lsub c member)
                have before : BagEq P (par (par (pFor t xt A) (pFor u yu B)) (pPar L)) := by
                  rw [bagEq_iff, components_par, components_par, components_pPar_leaves L leavesL,
                    components_pFor, components_pFor]
                  exact (permC₁.trans (permC₂.cons _)).map close
                have leavesRest : ∀ c ∈ rest, components c = [c] := fun c member =>
                  leaf_of_mem_closed_components (restClosed c (perm₂.symm.subset (List.mem_cons_of_mem _ member)))
                have closedRest : rest.map close = rest := by
                  conv_rhs => rw [← List.map_id rest]
                  exact List.map_congr_left fun c member =>
                    close_of_mem_closed_components (restClosed c (perm₂.symm.subset (List.mem_cons_of_mem _ member)))
                have after : BagEq (par r (pPar L)) (pPar (r :: rest)) := by
                  rw [bagEq_iff, components_par, components_pPar_leaves L leavesL]
                  have : components (pPar (r :: rest)) = components r ++ rest := by
                    simp only [pPar, components, componentsList, componentsList_eq_flatMap]
                    rw [List.flatMap_congr (g := fun c => [c]) leavesRest, List.flatMap_singleton']
                  rw [this, List.map_append, List.map_append, closedRest]
                  exact List.Perm.append_left _ permL
                exact .congruence before step₁ after
      · subst closeC₁
        obtain ⟨X, A, rfl, rfl, rfl⟩ := closeIn_eq_pReflect reflShape
        have calcs := calcTerm_pReflect (calcTerm_of_mem_components inCalc C₁mem)
        have freshA : ∀ z ∈ pvars (close A), z ∈ avoid := by
          intro z occurs
          apply fresh z
          apply pvars_close_of_mem_components C₁mem
          unfold close at occurs ⊢
          rw [closeIn_pReflect, pvars_pReflect]
          exact List.mem_append_right _ occurs
        have inner := ih A calcs.2 freshA a' a'In
        have step₁ : BagStep conventional (par (pReflect X A) (pPar L₁))
            (par (pFor (tProc a') X pZero) (pPar L₁)) := .parallel _ (.reflect X inner)
        have L₁sub : ∀ c ∈ L₁, c ∈ components P := fun c member =>
          permC₁.symm.subset (List.mem_cons_of_mem _ member)
        have leavesL₁ : ∀ c ∈ L₁, components c = [c] := fun c member => leafAll c (L₁sub c member)
        have reflLeaf : components (pReflect X A) = [pReflect X A] := by
          have := leafAll _ C₁mem
          exact this
        have before : BagEq P (par (pReflect X A) (pPar L₁)) := by
          rw [bagEq_iff, components_par, components_pPar_leaves L₁ leavesL₁, reflLeaf]
          exact permC₁.map close
        have leavesRest : ∀ c ∈ rest₁, components c = [c] := fun c member =>
          leaf_of_mem_closed_components (restClosed c member)
        have closedRest : rest₁.map close = rest₁ := by
          conv_rhs => rw [← List.map_id rest₁]
          exact List.map_congr_left fun c member => close_of_mem_closed_components (restClosed c member)
        have after : BagEq (par (pFor (tProc a') X pZero) (pPar L₁))
            (pPar (pFor (tProc a') (closeIn [] X) pZero :: rest₁)) := by
          rw [bagEq_iff, components_par, components_pPar_leaves L₁ leavesL₁, components_pFor]
          have : components (pPar (pFor (tProc a') (closeIn [] X) pZero :: rest₁)) =
              pFor (tProc a') (closeIn [] X) pZero :: rest₁ := by
            simp only [pPar, components, componentsList, componentsList_eq_flatMap]
            rw [List.flatMap_congr (g := fun c => [c]) leavesRest, List.flatMap_singleton', components_pFor]
            rfl
          rw [this, List.singleton_append, List.map_cons, List.map_cons, closedRest]
          have channel : close (pFor (tProc a') X pZero) = close (pFor (tProc a') (closeIn [] X) pZero) :=
            alphaEq_pFor_channel (tProc a') X pZero
          rw [channel]
          exact List.Perm.cons _ permL₁
        exact .congruence before step₁ after

/-- **Soundness modulo the bag laws.** -/
theorem cstepBag_sound {P Q : Pattern} (inCalc : calcTerm P = true) (member : Q ∈ cstepBag P) :
    BagStep conventional P Q :=
  stepComps_sound (pvars (close P)) _ P inCalc (fun _ occurs => occurs) Q member

/-! ## Completeness modulo the bag laws, for COMM at any position -/

theorem comm_mem_stepComps {avoid : List String} {fuel : ℕ} {cs rest₁ rest : List Pattern}
    {c₁ c₂ r : Pattern} (first : (c₁, rest₁) ∈ picks cs) (second : (c₂, rest) ∈ picks rest₁)
    (fired : r ∈ commClosed avoid c₁ c₂) : pPar (r :: rest) ∈ stepComps avoid (fuel + 1) cs := by
  simp only [stepComps, List.mem_flatMap, List.mem_append]
  exact ⟨(c₁, rest₁), first, .inl ⟨(c₂, rest), second, List.mem_map_of_mem fired⟩⟩

theorem refl_mem_stepComps {avoid : List String} {fuel : ℕ} {cs rest₁ : List Pattern} {x a a' : Pattern}
    (first : (pReflect x a, rest₁) ∈ picks cs) (inner : a' ∈ stepComps avoid fuel (components a)) :
    pPar (pFor (tProc a') x pZero :: rest₁) ∈ stepComps avoid (fuel + 1) cs := by
  simp only [stepComps, List.mem_flatMap, List.mem_append]
  refine ⟨(pReflect x a, rest₁), first, .inr ?_⟩
  simp only [pReflect]
  exact List.mem_map_of_mem inner

theorem components_pPar_cons (r : Pattern) (rest : List Pattern) :
    components (pPar (r :: rest)) = components r ++ rest.flatMap components := by
  simp [pPar, components, componentsList, componentsList_eq_flatMap]

/-- A step of some components is a step of more components. -/
theorem stepComps_append {avoid : List String} {fuel : ℕ} {cs : List Pattern} (ms : List Pattern)
    (leaves : ∀ m ∈ ms, components m = [m]) {Q₁ : Pattern}
    (member : Q₁ ∈ stepComps avoid (fuel + 1) cs) :
    ∃ Q₂ ∈ stepComps avoid (fuel + 1) (cs ++ ms), components Q₂ = components Q₁ ++ ms := by
  have msFlat : ms.flatMap components = ms := by
    rw [List.flatMap_congr (g := fun c => [c]) leaves, List.flatMap_singleton']
  obtain ⟨c₁, rest₁, first, which⟩ := mem_stepComps member
  rcases which with ⟨c₂, rest, r, second, fired, rfl⟩ | ⟨x, a, a', rfl, inner, rfl⟩
  · refine ⟨pPar (r :: (rest ++ ms)), comm_mem_stepComps (mem_picks_append ms first)
      (mem_picks_append ms second) fired, ?_⟩
    rw [components_pPar_cons, components_pPar_cons, List.flatMap_append, msFlat, List.append_assoc]
  · refine ⟨pPar (pFor (tProc a') x pZero :: (rest₁ ++ ms)),
      refl_mem_stepComps (mem_picks_append ms first) inner, ?_⟩
    rw [components_pPar_cons, components_pPar_cons, List.flatMap_append, msFlat, List.append_assoc]

/-- Reordering the components reorders the reducts' components. -/
theorem stepComps_perm {avoid : List String} {fuel : ℕ} {cs cs' : List Pattern} (perm : cs.Perm cs')
    {Q₁ : Pattern} (member : Q₁ ∈ stepComps avoid (fuel + 1) cs') :
    ∃ Q₂ ∈ stepComps avoid (fuel + 1) cs, (components Q₂).Perm (components Q₁) := by
  obtain ⟨c₁, rest₁, first, which⟩ := mem_stepComps member
  obtain ⟨rest₁', first', perm₁⟩ := mem_picks_of_perm (perm.trans (perm_of_mem_picks first))
  rcases which with ⟨c₂, rest, r, second, fired, rfl⟩ | ⟨x, a, a', rfl, inner, rfl⟩
  · obtain ⟨rest', second', perm₂⟩ := mem_picks_of_perm (perm₁.trans (perm_of_mem_picks second))
    refine ⟨pPar (r :: rest'), comm_mem_stepComps first' second' fired, ?_⟩
    rw [components_pPar_cons, components_pPar_cons]
    exact List.Perm.append_left _ (perm₂.flatMap_right components)
  · refine ⟨pPar (pFor (tProc a') x pZero :: rest₁'), refl_mem_stepComps first' inner, ?_⟩
    rw [components_pPar_cons, components_pPar_cons]
    exact List.Perm.append_left _ (perm₁.flatMap_right components)

theorem pvars_in_components (X : Pattern) : ∀ z ∈ pvars X, ∃ c ∈ components X, z ∈ pvars c := by
  induction X using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ z ∈ pvars q, ∃ c ∈ components q, z ∈ pvars c) with
  | collection ct elems rest ih =>
      intro z occurs
      by_cases isBag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := isBag
        simp only [pvars, pvarsList_eq_flatMap, List.mem_flatMap] at occurs
        obtain ⟨q, inside, inQ⟩ := occurs
        obtain ⟨c, cIn, zIn⟩ := ih q inside z inQ
        refine ⟨c, ?_, zIn⟩
        simp only [components, componentsList_eq_flatMap, List.mem_flatMap]
        exact ⟨q, inside, cIn⟩
      · have plain : components (.collection ct elems rest) = [.collection ct elems rest] := by
          rcases ct <;> rcases rest <;> simp_all [components]
        exact ⟨_, by rw [plain]; exact List.mem_singleton_self _, occurs⟩
  | apply c args ih =>
      intro z occurs
      by_cases zero : c = "MZero" ∧ args = []
      · obtain ⟨rfl, rfl⟩ := zero; simp [pvars, pvars.pvarsList] at occurs
      · have plain : components (.apply c args) = [.apply c args] := by
          unfold components; split <;> simp_all
        exact ⟨_, by rw [plain]; exact List.mem_singleton_self _, occurs⟩
  | bvar n => intro z occurs; simp [pvars] at occurs
  | fvar x => intro z occurs; exact ⟨_, by simp [components], occurs⟩
  | lambda nm body ih => intro z occurs; exact ⟨_, by simp [components], occurs⟩
  | multiLambda n nms body ih => intro z occurs; exact ⟨_, by simp [components], occurs⟩
  | subst body repl ihb ihr => intro z occurs; exact ⟨_, by simp [components], occurs⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member z occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head z occurs
      · exact tail q later z occurs

theorem components_close_pFor (t x k : Pattern) : components (close (pFor t x k)) = [close (pFor t x k)] := by
  unfold close; rw [closeIn_pFor]; exact components_pFor _ _ _

/-- **Completeness modulo the bag laws, for COMM at any position.** Every step
of the closing fragment built from COMM, PAR and the bag laws is matched, up
to the bag laws, by a step of the closed components. -/
theorem stepComps_complete {P Q : Pattern} (step : BagCommStep closing P Q) :
    ∀ (avoid : List String) (fuel : ℕ), (∀ z ∈ pvars (close P), z ∈ avoid) →
      ∃ Q' ∈ stepComps avoid (fuel + 1) (components (close P)), BagEq Q' Q := by
  induction step with
  | comm t u x A B bs principal admitted =>
      intro avoid fuel fresh
      obtain ⟨Q₀, fired, alpha⟩ := commClosed_complete avoid t u x A B bs principal admitted fresh
      have comps : components (close (par (pFor t x A) (pFor u x B))) =
          [close (pFor t x A), close (pFor u x B)] := by
        unfold close
        rw [closeIn_par, components_par]
        exact congrArg₂ (· ++ ·) (components_close_pFor t x A) (components_close_pFor u x B)
      refine ⟨pPar [Q₀], ?_, ?_⟩
      · rw [comps]
        exact comm_mem_stepComps (rest₁ := [close (pFor u x B)]) (by simp [picks]) (by simp [picks]) fired
      · unfold BagEq
        have : components (close (pPar [Q₀])) = components (close Q₀) := by
          unfold close
          simp [pPar, closeIn, closeList, components, componentsList]
        rw [this, show close Q₀ = close _ from alpha]
  | parallel R _ ih =>
      rename_i source target stepS
      intro avoid fuel fresh
      have split : components (close (par source R)) = components (close source) ++ components (close R) := by
        unfold close; rw [closeIn_par, components_par]
      obtain ⟨Q₁, member, alpha⟩ := ih avoid fuel fun z occurs => fresh z (by
        unfold close at occurs ⊢; rw [closeIn_par, pvars_par]; exact List.mem_append_left _ occurs)
      have leavesR : ∀ m ∈ components (close R), components m = [m] := fun m member =>
        leaf_of_mem_closed_components member
      obtain ⟨Q₂, member₂, comps₂⟩ := stepComps_append (components (close R)) leavesR member
      refine ⟨Q₂, by rw [split]; exact member₂, ?_⟩
      rw [bagEq_iff] at alpha ⊢
      have closedR : (components (close R)).map close = (components (close R)) := by
        conv_rhs => rw [← List.map_id (components (close R))]
        exact List.map_congr_left fun c member => close_of_mem_closed_components member
      rw [comps₂, components_par, List.map_append, List.map_append, closedR]
      have : components (close R) = (components R).map close := components_closeIn R []
      rw [this]
      exact List.Perm.append_right _ alpha
  | congruence before _ after ih =>
      rename_i source source' target' target stepS
      intro avoid fuel fresh
      have freshSource' : ∀ z ∈ pvars (close source'), z ∈ avoid := by
        intro z occurs
        obtain ⟨c, cIn, zIn⟩ := pvars_in_components _ z occurs
        have cInSource : c ∈ components (close source) := (show List.Perm _ _ from before).symm.subset cIn
        exact fresh z (pvars_of_mem_components cInSource zIn)
      obtain ⟨Q₁, member, alpha⟩ := ih avoid fuel freshSource'
      obtain ⟨Q₂, member₂, perm⟩ := stepComps_perm (show List.Perm _ _ from before) member
      refine ⟨Q₂, member₂, ?_⟩
      have : BagEq Q₂ Q₁ := by
        rw [bagEq_iff]; exact perm.map close
      exact this.trans (alpha.trans after)

/-- **Completeness of the step modulo the bag laws** for COMM at any position. -/
theorem cstepBag_complete {P Q : Pattern} (step : BagCommStep closing P Q) :
    ∃ Q' ∈ cstepBag P, BagEq Q' Q :=
  stepComps_complete step (pvars (close P)) (psize (close P)) fun _ occurs => occurs

/-! ## Reflection modulo the bag laws quotes a representative -/

namespace BagControls

def atomA : Pattern := .apply "A" []
def atomB : Pattern := .apply "B" []

/-- `for(0 <- @0) A | for(0 <- @0) B`: one COMM gives `A | B`. -/
def twoParties : Proc := par (pFor pZero demoChan atomA) (pFor pZero demoChan atomB)

def reflected : Proc := pReflect demoChan twoParties

def listenerAB : Proc := pFor (tProc (par atomA atomB)) demoChan pZero
def listenerBA : Proc := pFor (tProc (par atomB atomA)) demoChan pZero

theorem principal_empty : Principal pZero pZero [] := by
  refine ⟨rfl, ?_, by simp⟩
  intro τ _ p
  congr 1
  exact Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_none p

theorem parties_step : BagStep conventional twoParties (par atomA atomB) := by
  have step := BagStep.comm (admit := conventional) pZero pZero demoChan atomA atomB [] principal_empty
    ⟨by simp [pZero, pvars, pvars.pvarsList], by simp [pZero, pvars, pvars.pvarsList],
      by simp [pZero, pvars, pvars.pvarsList], by simp [pZero, pvars, pvars.pvarsList],
      by simp [pZero, pvars, pvars.pvarsList]⟩
  simpa [twoParties, applyDot, dotBindings, applyBindings, atomA, atomB] using step

/-- Under the bag laws, the reflected process reaches both listeners. -/
theorem reflects_both :
    BagStep conventional reflected listenerAB ∧ BagStep conventional reflected listenerBA := by
  refine ⟨.reflect demoChan parties_step, .reflect demoChan ?_⟩
  exact .congruence (BagEq.refl _) parties_step (BagEq.par_comm atomA atomB)

/-- The two listeners are not equivalent: the bag laws do not act inside a
pattern. -/
theorem listeners_differ : ¬ BagEq listenerAB listenerBA := by
  unfold BagEq; decide +kernel

/-- A partner whose pattern quotes `A | B` communicates with one listener and
not with the other: unification compares patterns as written. -/
def partner : Proc := pFor (tProc (par atomA atomB)) demoChan pZero

theorem partner_tells_listeners_apart :
    cstep (par listenerAB partner) ≠ [] ∧ cstep (par listenerBA partner) = [] := by
  constructor <;> decide +kernel

/-- The executable quotes the representatives its own COMM produces: the reduct
in each order, wrapped in the parallel composition it rebuilds. Neither is
equivalent to the relational listeners above. -/
theorem executable_quotes_representatives :
    cstepBag reflected =
      [pPar [pFor (tProc (pPar [par atomA atomB])) demoChan pZero],
        pPar [pFor (tProc (pPar [par atomB atomA])) demoChan pZero]] ∧
      ¬ BagEq (pPar [pFor (tProc (pPar [par atomA atomB])) demoChan pZero]) listenerAB := by
  constructor
  · decide +kernel
  · unfold BagEq; decide +kernel

end BagControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
