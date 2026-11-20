import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowHosting

/-!
# Scope and formation of the structural scanner's actual source clauses

The proofs retain the compiled binder-key family and the existing prefix
sites. Constructor equations use a root probe and at most three child scans;
all successful returns are held marker data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScanner

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

theorem support_tupleAt {X : Type} {declaration : X → MetaArity MSig}
    (children : List (Term (signature MSig declaration) [] ())) :
    support (Toolkit.tupleAt children) = children.flatMap support := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
      change support first ++ supportArgs (Toolkit.tupleArgsAt rest) = support first ++ rest.flatMap support
      change supportArgs (Toolkit.tupleArgsAt rest) = rest.flatMap support at ih
      rw [ih]

@[simp] theorem support_nodeAt {X : Type} {declaration : X → MetaArity MSig}
    (tag : String) (children : List (Term (signature MSig declaration) [] ())) :
    support (nodeAt tag children) = children.flatMap support := by
  simp only [nodeAt, support_tupleAt, List.flatMap_cons, Toolkit.symAt, support, supportArgs,
    List.nil_append]

@[simp] theorem support_marker {X : Type} (declaration : X → MetaArity MSig) :
    support (marker declaration) = [] := rfl

@[simp] theorem support_stopAt {X : Type} (declaration : X → MetaArity MSig) :
    support (stopAt declaration) = [] := rfl

@[simp] theorem support_scanAt {X : Type} {declaration : X → MetaArity MSig}
    (term : Term (signature MSig declaration) [] ()) : support (scanAt term) = support term := by
  simp only [scanAt, support_nodeAt, List.flatMap_cons, List.flatMap_nil, List.append_nil]

@[simp] theorem support_rootAt {X : Type} {declaration : X → MetaArity MSig}
    (term : Term (signature MSig declaration) [] ()) : support (rootAt term) = support term := by
  simp only [rootAt, support_nodeAt, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    support_stopAt]

@[simp] theorem support_probeAt {X : Type} {declaration : X → MetaArity MSig}
    (term : Term (signature MSig declaration) [] ()) : support (probeAt term) = support term := by
  change support (nodeAt NormalProbe.probeTag [rootAt term]) = support term
  simp only [support_nodeAt, List.flatMap_cons, List.flatMap_nil, List.append_nil, support_rootAt]

theorem names_nodeAt {κ : Keys MSig} (allowed : List κ.Site) (tag : String)
    (children : List (Data κ [] ()))
    (known : ∀ child ∈ children, NamesIn allowed child) : NamesIn allowed (nodeAt tag children) := by
  intro name member
  rw [support_nodeAt] at member
  obtain ⟨child, inside, used⟩ := List.mem_flatMap.mp member
  exact known child inside name used

@[simp] theorem names_marker {κ : Keys MSig} (allowed : List κ.Site) :
    NamesIn allowed (marker (fam κ)) := by
  intro name member
  rw [support_marker] at member
  cases member

@[simp] theorem names_scanAt {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (scanAt term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_scanAt]

@[simp] theorem names_probeAt {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (probeAt term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_probeAt]

variable {dev : NativeTypesOnTheStep.Computing.Definitions.Development} (built : Compiled dev)

theorem names_datum (allowed : List (BinderCore.keys built.rules).Site)
    (inside : site built 0 ∈ allowed) (index : Fin 3) :
    NamesIn allowed (datum built index) := by
  intro name member
  change name ∈ support (generator (fam (BinderCore.keys built.rules)) ⟨[], key built index⟩) at member
  have same : name = ⟨[], key built index⟩ := by
    simpa only [support_generator, List.mem_singleton] using member
  subst name
  exact ⟨rfl, inside⟩

theorem names_pattern (allowed : List (BinderCore.keys built.rules).Site)
    (inside : site built 0 ∈ allowed) (kind : Constructor) :
    NamesIn allowed (pattern built kind) := by
  apply names_nodeAt
  intro child member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact names_datum built allowed inside index

theorem childTests_scoped (allowed : List (BinderCore.keys built.rules).Site)
    (inside : site built 0 ∈ allowed) (kind : Constructor) {Ty : Type} :
    (childTests built (Ty := Ty) kind).Scoped allowed := by
  cases kind <;> dsimp only [childTests, childTest, Comp.Scoped]
  all_goals repeat' constructor
  all_goals first
    | exact names_marker _
    | apply (names_scanAt _ _).mpr
      apply names_datum built
      simp [inside]

theorem equation_scoped (D : Discipline MSig [] ()) (kind : Constructor) :
    (equation built D kind).Scoped := by
  refine ⟨(names_scanAt _ _).mpr (names_pattern built _ List.mem_cons_self kind), ?_⟩
  change NamesIn [site built 0] (probeAt (pattern built kind)) ∧
    NamesIn [site built 1, site built 0] (probeAt (pattern built kind)) ∧
    (childTests built (Ty := D.Ty) kind).Scoped [site built 1, site built 0]
  exact ⟨(names_probeAt _ _).mpr (names_pattern built _ List.mem_cons_self kind),
    (names_probeAt _ _).mpr (names_pattern built _ (by simp) kind),
    childTests_scoped built _ (by simp) kind⟩

theorem equation_distinct (D : Discipline MSig [] ()) (kind : Constructor) :
    ((equation built D kind).site :: (equation built D kind).rhs.sites).Nodup := by
  have scalar : ([0, 1] : List (Fin 5)).Nodup := by decide +kernel
  have unary : ([0, 1, 2] : List (Fin 5)).Nodup := by decide +kernel
  have binary : ([0, 1, 2, 3] : List (Fin 5)).Nodup := by decide +kernel
  have ternary : ([0, 1, 2, 3, 4] : List (Fin 5)).Nodup := by decide +kernel
  cases kind <;> first
    | exact scalar.map (site_injective built)
    | exact unary.map (site_injective built)
    | exact binary.map (site_injective built)
    | exact ternary.map (site_injective built)

theorem equation_arrows (D : Discipline MSig [] ()) (kind : Constructor) :
    Hosting.ArrowComp (equation built D kind).rhs := by
  cases kind <;> simp [equation, rootTest, childTests, childTest, Hosting.ArrowComp]

theorem equations_formed (D : Discipline MSig [] ()) :
    ∀ clause ∈ equations built D,
      clause.Scoped ∧ (clause.site :: clause.rhs.sites).Nodup ∧ Hosting.ArrowComp clause.rhs := by
  intro clause member
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp member
  exact ⟨equation_scoped built D kind, equation_distinct built D kind, equation_arrows built D kind⟩

theorem query_scoped (term : MClosed) {Ty : Type} :
    (query built (Ty := Ty) term).Scoped [site built 0] := by
  change NamesIn [site built 0] (scanAt (Rigid.includeTerm (fam (BinderCore.keys built.rules)) term))
  rw [names_scanAt]
  intro name member
  rw [Rigid.support_include] at member
  cases member

theorem query_distinct (term : MClosed) {Ty : Type} :
    (site built 0 :: (query built (Ty := Ty) term).sites).Nodup := List.nodup_singleton _

theorem query_arrows (term : MClosed) {Ty : Type} :
    Hosting.ArrowComp (query built (Ty := Ty) term) := by trivial

theorem pi_lambda_id_formed (D : Discipline MSig [] ()) :
    (equation built D .pi).Scoped ∧ (equation built D .lam).Scoped ∧
      (equation built D .id).Scoped ∧
      ((equation built D .id).site :: (equation built D .id).rhs.sites).Nodup :=
  ⟨equation_scoped built D .pi, equation_scoped built D .lam,
    equation_scoped built D .id, equation_distinct built D .id⟩

def piExample : Tower.Tm 0 := .pi TowerVectorsModel.numC TowerVectorsModel.numC
def lambdaExample : Tower.Tm 0 := .lam (.var 0)
def idExample : Tower.Tm 0 :=
  .id TowerVectorsModel.numC TowerVectorsModel.zeroC TowerVectorsModel.zeroC

theorem named_queries_scoped {Ty : Type} :
    (query built (Ty := Ty) (encodeTm piExample)).Scoped [site built 0] ∧
      (query built (Ty := Ty) (encodeTm lambdaExample)).Scoped [site built 0] ∧
      (query built (Ty := Ty) (encodeTm idExample)).Scoped [site built 0] :=
  ⟨query_scoped built _, query_scoped built _, query_scoped built _⟩

def repeatedSiteExample {Ty : Type} : Comp (BinderCore.keys built.rules) [] () Ty :=
  childTest built 2 0 (childTest built 2 1 (.ret (marker (fam (BinderCore.keys built.rules)))))

theorem repeated_let_site_rejected {Ty : Type} :
    ¬ (site built 0 :: (repeatedSiteExample built (Ty := Ty)).sites).Nodup := by
  simp [repeatedSiteExample, childTest, Comp.sites]

theorem instantiate_nodeAt {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) (tag : String)
    (children : List (Term (signature MSig source) [] ())) :
    instantiate assignment (nodeAt tag children) = nodeAt tag (children.map (instantiate assignment)) := by
  unfold nodeAt
  rw [RuleBuilder.instantiate_tuple]
  rfl

@[simp] theorem instantiate_scanAt {X Y : Type} {source : X → MetaArity MSig}
    {target : Y → MetaArity MSig} (assignment : Assignment source target)
    (term : Term (signature MSig source) [] ()) :
    instantiate assignment (scanAt term) = scanAt (instantiate assignment term) := by
  simp only [scanAt, instantiate_nodeAt, List.map_cons, List.map_nil]

@[simp] theorem instantiate_stopAt {X Y : Type} {source : X → MetaArity MSig}
    {target : Y → MetaArity MSig} (assignment : Assignment source target) :
    instantiate assignment (stopAt source) = stopAt target := rfl

@[simp] theorem instantiate_marker {X Y : Type} {source : X → MetaArity MSig}
    {target : Y → MetaArity MSig} (assignment : Assignment source target) :
    instantiate assignment (marker source) = marker target := rfl

@[simp] theorem instantiate_rootAt {X Y : Type} {source : X → MetaArity MSig}
    {target : Y → MetaArity MSig} (assignment : Assignment source target)
    (term : Term (signature MSig source) [] ()) :
    instantiate assignment (rootAt term) = rootAt (instantiate assignment term) := by
  simp only [rootAt, instantiate_nodeAt, List.map_cons, List.map_nil, instantiate_stopAt]

@[simp] theorem instantiate_probeAt {X Y : Type} {source : X → MetaArity MSig}
    {target : Y → MetaArity MSig} (assignment : Assignment source target)
    (term : Term (signature MSig source) [] ()) :
    instantiate assignment (probeAt term) = probeAt (instantiate assignment term) := by
  simp only [probeAt, NormalProbe.instantiate_wrap, instantiate_rootAt]

theorem instantiate_pattern {X : Type} {target : X → MetaArity MSig}
    (assignment : Assignment (fam (BinderCore.keys built.rules)) target) (kind : Constructor) :
    instantiate assignment (pattern built kind) =
      nodeAt kind.tag (kind.fields.map fun index => instantiate assignment (datum built index)) := by
  simp only [pattern, instantiate_nodeAt, List.map_map, Function.comp_def]

@[simp] theorem literalHead_nodeAt {X : Type} {target : X → MetaArity MSig}
    (tag : String) (children : List (Term (signature MSig target) [] ())) :
    literalHead (nodeAt tag children) = some tag := rfl

@[simp] theorem literalHead_scanAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) : literalHead (scanAt term) = some scanTag := rfl

@[simp] theorem literalHead_rootAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) : literalHead (rootAt term) = some activeTag := rfl

@[simp] theorem literalHead_probeAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) :
    literalHead (probeAt term) = some NormalProbe.probeTag := rfl

theorem equation_head (D : Discipline MSig [] ()) (kind : Constructor) :
    literalHead (equation built D kind).lhs = some scanTag := rfl

theorem scanAt_eq_iff {X : Type} {target : X → MetaArity MSig}
    (first second : Term (signature MSig target) [] ()) :
    scanAt first = scanAt second ↔ first = second :=
  ⟨fun same => (Toolkit.tuple2_inj same).2, congrArg scanAt⟩

theorem rootAt_eq_iff {X : Type} {target : X → MetaArity MSig}
    (first second : Term (signature MSig target) [] ()) :
    rootAt first = rootAt second ↔ first = second :=
  ⟨fun same => (Toolkit.tuple3_inj (Toolkit.tuple2_inj same).2).2.1, congrArg rootAt⟩

theorem probeAt_eq_iff {X : Type} {target : X → MetaArity MSig}
    (first second : Term (signature MSig target) [] ()) :
    probeAt first = probeAt second ↔ first = second :=
  (NormalProbe.wrap_eq_iff _ _).trans (rootAt_eq_iff first second)

theorem include_nodeAt {X : Type} (target : X → MetaArity MSig)
    (tag : String) (children : List MClosed) :
    Rigid.includeTerm target (nodeC tag children) = nodeAt tag (children.map (Rigid.includeTerm target)) :=
  DataEmbedding.include_nodeC target tag children

theorem include_rootAt {X : Type} (target : X → MetaArity MSig) (term : MClosed) :
    Rigid.includeTerm target (rootC term (csym stopTag)) = rootAt (Rigid.includeTerm target term) := by
  simp only [rootC, activeC, include_nodeAt, List.map_cons, List.map_nil]
  rfl

theorem copy_datum (scope : Nat) (index : Fin 3) :
    instantiate (copyAt (BinderCore.keys built.rules) scope) (datum built index) =
      nameAt (BinderCore.keys built.rules) [scope] (key built index) := by
  change instantiate (copyAt (BinderCore.keys built.rules) scope)
    (generator (fam (BinderCore.keys built.rules)) ⟨[], key built index⟩) = _
  rw [instantiate_generator]
  rfl

theorem open_datum (bindSite : Fin 5) (different : bindSite ≠ 0) (scope : Nat)
    (scopes : List Nat) (index : Fin 3) :
    instantiate (openAt (BinderCore.keys built.rules) (site built bindSite) scope)
      (nameAt (BinderCore.keys built.rules) scopes (key built index)) =
        nameAt (BinderCore.keys built.rules) scopes (key built index) := by
  have separate : site built 0 ≠ site built bindSite := by
    intro same
    exact different ((site_injective built same).symm)
  change instantiate (openAt (BinderCore.keys built.rules) (site built bindSite) scope)
    (generator (fam (BinderCore.keys built.rules)) ⟨scopes, key built index⟩) = _
  rw [instantiate_generator]
  change generator (fam (BinderCore.keys built.rules))
    ⟨if site built 0 = site built bindSite then scope :: scopes else scopes, key built index⟩ = _
  rw [if_neg separate]
  rfl

theorem constructors_count : Constructor.all.length = 12 := rfl

theorem constructor_list_complete (kind : Constructor) : kind ∈ Constructor.all := by
  cases kind <;> simp [Constructor.all]

section Encoding

variable {X : Type} (target : X → MetaArity MSig)

@[simp] theorem include_encoded_var {n : Nat} (index : Fin n) :
    Rigid.includeTerm target (encodeTm (.var index : Tower.Tm n)) =
      nodeAt "prime-tm-var" [Rigid.includeTerm target (encodeNat index.val)] := by
  rw [encodeTm_var, include_nodeAt]
  rfl

@[simp] theorem include_encoded_const {n : Nat} (name : DeclName) :
    Rigid.includeTerm target (encodeTm (.const name : Tower.Tm n)) =
      nodeAt "prime-tm-const" [Rigid.includeTerm target (encodeName name)] := by
  rw [encodeTm_const, include_nodeAt]
  rfl

@[simp] theorem include_encoded_head {n : Nat} (head : Tower.Head) :
    Rigid.includeTerm target (encodeTm (.head head : Tower.Tm n)) =
      nodeAt "prime-tm-head" [Rigid.includeTerm target (encodeHead head)] := by
  rw [encodeTm_head, include_nodeAt]
  rfl

@[simp] theorem include_encoded_pi {n : Nat} (domain : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    Rigid.includeTerm target (encodeTm (.pi domain body)) =
      nodeAt "prime-tm-pi" [Rigid.includeTerm target (encodeTm domain),
        Rigid.includeTerm target (encodeTm body)] := by
  rw [encodeTm_pi, include_nodeAt]
  rfl

@[simp] theorem include_encoded_sigma {n : Nat} (domain : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    Rigid.includeTerm target (encodeTm (.sigma domain body)) =
      nodeAt "prime-tm-sigma" [Rigid.includeTerm target (encodeTm domain),
        Rigid.includeTerm target (encodeTm body)] := by
  rw [encodeTm_sigma, include_nodeAt]
  rfl

@[simp] theorem include_encoded_id {n : Nat} (carrier left right : Tower.Tm n) :
    Rigid.includeTerm target (encodeTm (.id carrier left right)) =
      nodeAt "prime-tm-id" [Rigid.includeTerm target (encodeTm carrier),
        Rigid.includeTerm target (encodeTm left), Rigid.includeTerm target (encodeTm right)] := by
  rw [encodeTm_id, include_nodeAt]
  rfl

@[simp] theorem include_encoded_lam {n : Nat} (body : Tower.Tm (n + 1)) :
    Rigid.includeTerm target (encodeTm (.lam body)) =
      nodeAt "prime-tm-lam" [Rigid.includeTerm target (encodeTm body)] := by
  rw [encodeTm_lam, include_nodeAt]
  rfl

@[simp] theorem include_encoded_app {n : Nat} (function argument : Tower.Tm n) :
    Rigid.includeTerm target (encodeTm (.app function argument)) =
      nodeAt "prime-tm-app" [Rigid.includeTerm target (encodeTm function),
        Rigid.includeTerm target (encodeTm argument)] := by
  rw [encodeTm_app, include_nodeAt]
  rfl

@[simp] theorem include_encoded_pair {n : Nat} (first second : Tower.Tm n) :
    Rigid.includeTerm target (encodeTm (.pair first second)) =
      nodeAt "prime-tm-pair" [Rigid.includeTerm target (encodeTm first),
        Rigid.includeTerm target (encodeTm second)] := by
  rw [encodeTm_pair, include_nodeAt]
  rfl

@[simp] theorem include_encoded_fst {n : Nat} (term : Tower.Tm n) :
    Rigid.includeTerm target (encodeTm (.fst term)) =
      nodeAt "prime-tm-fst" [Rigid.includeTerm target (encodeTm term)] := by
  rw [encodeTm_fst, include_nodeAt]
  rfl

@[simp] theorem include_encoded_snd {n : Nat} (term : Tower.Tm n) :
    Rigid.includeTerm target (encodeTm (.snd term)) =
      nodeAt "prime-tm-snd" [Rigid.includeTerm target (encodeTm term)] := by
  rw [encodeTm_snd, include_nodeAt]
  rfl

@[simp] theorem include_encoded_refl {n : Nat} (term : Tower.Tm n) :
    Rigid.includeTerm target (encodeTm (.refl term)) =
      nodeAt "prime-tm-refl" [Rigid.includeTerm target (encodeTm term)] := by
  rw [encodeTm_refl, include_nodeAt]
  rfl

end Encoding

theorem marker_ne_redex {X : Type} (target : X → MetaArity MSig) :
    marker target ≠ NormalProbe.marker target := by
  intro same
  have tags := congrArg literalSymbol same
  exact (by decide +kernel : ("hd-normal" : String) ≠ "hd-redex-found") (Option.some.inj tags)

theorem marker_ne_probe {X : Type} (target : X → MetaArity MSig)
    (term : Term (signature MSig target) [] ()) : marker target ≠ probeAt term := by
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScanner

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScanner.equations_formed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScanner.repeated_let_site_rejected
