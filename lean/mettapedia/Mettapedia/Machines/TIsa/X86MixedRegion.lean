import Mettapedia.Machines.TIsa.X86DataPrimitive

/-!
# Word operations, shifts and branches in one checked resource region

Nodes are a compilation presentation of existing Control.Row and
Control.Branch recipes. The liveness certificate is checked at every edge;
readbacks cover only the current live set. Source execution remains the
existing resource system and its MultiStep relation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MixedRegion
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Key := Fin 12
abbrev Location := Control.Location Key
abbrev Values := Location → Word
abbrev World := Multiset (Cells.Cell Location)
abbrev LiveMap := Word → Finset Key
abbrev physical := X86DataPrimitive.physical

structure WordSite where
  activation : Nat
  point : Word
  next : Word
  instruction : X86DataPrimitive.Instruction

def WordSite.row (site : WordSite) : Control.Row Key :=
  ⟨site.activation,site.point,site.next,X86DataPrimitive.effect site.instruction⟩

inductive Node where
  | word (site : WordSite)
  | branch (branch : Control.Branch Key)

def Node.activation : Node → Nat
  | .word site => site.activation
  | .branch choice => choice.activation
def Node.point : Node → Word
  | .word site => site.point
  | .branch choice => choice.point
def Node.next : Node → Word
  | .word site => site.next
  | .branch choice => choice.yes
def Node.recipe : Node → CellEffects.Recipe Location
  | .word site => site.row.recipe
  | .branch choice => choice.recipe
def Node.body : Node → List Chunk
  | .word site => [.bytes ((X86DataPrimitive.bytes site.instruction).map (BitVec.ofNat 8))]
  | .branch choice => X86BranchCompiler.body choice (physical choice.condition)
def Node.count : Node → Nat
  | .word site => X86DataPrimitive.count site.instruction
  | .branch _ => 2
def Node.writes : Node → Finset Register
  | .word site => X86DataPrimitive.writes site.instruction
  | .branch _ => X86BranchGate.writes

def Node.LiveOK (live : LiveMap) : Node → Prop
  | .word site => (X86DataPrimitive.effect site.instruction).inputs.toFinset ⊆ live site.point ∧
      live site.next ⊆ insert (X86DataPrimitive.destination site.instruction) (live site.point)
  | .branch choice => choice.condition ∈ live choice.point ∧
      live choice.yes ⊆ live choice.point ∧ live choice.no ⊆ live choice.point

instance (live : LiveMap) (node : Node) : Decidable (node.LiveOK live) := by
  cases node <;> exact inferInstanceAs (Decidable (_ ∧ _))

def entryName (finish : Word) : List Node → Word
  | [] => finish
  | node :: _ => node.point
def sites (nodes : List Node) : List Chunk := nodes.flatMap fun node => .label node.point.toNat :: node.body
def region (finish : Word) (nodes : List Node) : List Chunk := sites nodes ++ [.label finish.toNat]
def payload (finish : Word) : List Node → List Chunk
  | [] => []
  | node :: later => node.body ++ region finish later
def code (finish : Word) (nodes : List Node) (first tail : List Chunk) : List Chunk :=
  first ++ (region finish nodes ++ tail)

def Valid (live : LiveMap) (activation : Nat) (finish : Word) : List Node → Prop
  | [] => True
  | node :: later => node.activation = activation ∧ node.next = entryName finish later ∧
      node.LiveOK live ∧ Valid live activation finish later

instance (live : LiveMap) (activation : Nat) (finish : Word) (nodes : List Node) :
    Decidable (Valid live activation finish nodes) := by
  induction nodes with
  | nil => exact isTrue trivial
  | cons node later ih => exact inferInstanceAs (Decidable (_ ∧ _))

def compile? (live : LiveMap) (activation : Nat) (finish : Word) (nodes : List Node)
    (first tail : List Chunk) : Option Emission :=
  if Valid live activation finish nodes then assemble (code finish nodes first tail) else none

theorem compile?_iff (live : LiveMap) (activation : Nat) (finish : Word) (nodes : List Node)
    (first tail : List Chunk) (emission : Emission) :
    compile? live activation finish nodes first tail = some emission ↔
      Valid live activation finish nodes ∧ assemble (code finish nodes first tail) = some emission := by
  unfold compile?
  split <;> simp_all

theorem region_start (finish : Word) (nodes : List Node) :
    region finish nodes = .label (entryName finish nodes).toNat :: payload finish nodes := by
  cases nodes <;> simp [region,sites,entryName,payload,List.append_assoc]

theorem body_markers (node : Node) (cursor : Nat) (tail : List Chunk) :
    markersAt cursor (node.body ++ tail) = markersAt (cursor + width node.body) tail := by
  cases node <;> simp [Node.body,X86BranchCompiler.body,X86BranchCompiler.testBytes,
    markersAt,width,Chunk.width,prefixLength,Nat.add_assoc]

theorem valid_at (live : LiveMap) (activation : Nat) (finish : Word) (earlier : List Node) (node : Node)
    (later : List Node) (valid : Valid live activation finish (earlier ++ node :: later)) :
    node.activation = activation ∧ node.next = entryName finish later ∧ node.LiveOK live := by
  induction earlier with
  | nil => exact ⟨valid.1,valid.2.1,valid.2.2.1⟩
  | cons head rest ih => exact ih valid.2.2.2

structure Layout (live : LiveMap) (activation : Nat) (finish : Word) (nodes : List Node)
    (first tail : List Chunk) (emission : Emission) where
  valid : Valid live activation finish nodes
  labels : Labels
  resolved : labelsAt 0 (code finish nodes first tail) = some labels
  assembled : assemble (code finish nodes first tail) = some emission

theorem ofCompilation (live : LiveMap) (activation : Nat) (finish : Word) (nodes : List Node)
    (first tail : List Chunk) (emission : Emission)
    (accepted : compile? live activation finish nodes first tail = some emission) :
    Nonempty (Layout live activation finish nodes first tail emission) := by
  obtain ⟨valid,assembled⟩ := (compile?_iff live activation finish nodes first tail emission).mp accepted
  cases resolved : labelsAt 0 (code finish nodes first tail) with
  | none => simp [assemble,resolved] at assembled
  | some labels => exact ⟨⟨valid,labels,resolved,assembled⟩⟩

theorem Layout.site {live : LiveMap} {activation : Nat} {finish : Word} {nodes : List Node}
    {first tail : List Chunk} {emission : Emission} (layout : Layout live activation finish nodes first tail emission)
    (node : Node) (member : node ∈ nodes) :
    node.activation = activation ∧ node.LiveOK live ∧
      ∃ leading remaining, code finish nodes first tail =
        leading ++ (.label node.point.toNat :: (node.body ++ (.label node.next.toNat :: remaining))) := by
  obtain ⟨earlier,later,shape⟩ := List.mem_iff_append.mp member
  have valid : Valid live activation finish (earlier ++ node :: later) := by rw [← shape]; exact layout.valid
  obtain ⟨owner,flow,liveOK⟩ := valid_at live activation finish earlier node later valid
  refine ⟨owner,liveOK,first ++ sites earlier,payload finish later ++ tail,?_⟩
  calc
    code finish nodes first tail = first ++ (sites earlier ++ (region finish (node :: later) ++ tail)) := by
      simp [code,shape,region,sites,List.flatMap_append,List.append_assoc]
    _ = _ := by
      rw [region_start,entryName,payload,region_start,← flow]
      simp [List.append_assoc]

def footprint (nodes : List Node) : Finset Register := nodes.foldr (fun node acc => node.writes ∪ acc) ∅
theorem writes_in (nodes : List Node) (node : Node) (member : node ∈ nodes) : node.writes ⊆ footprint nodes := by
  induction nodes with
  | nil => cases member
  | cons head later ih =>
    rcases List.mem_cons.mp member with rfl | found
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih found) Finset.subset_union_right

structure Ready {live : LiveMap} {activation : Nat} {finish : Word} {nodes : List Node}
    {first tail : List Chunk} {emission : Emission} (layout : Layout live activation finish nodes first tail emission)
    (base : Int) (values : Values) (native : State) where
  origin : X86LegacyFetch.Basis native
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int)
  offset : Nat
  control : X86Assembler.lookup layout.labels (values (.inl activation)).toNat = some offset
  location : origin.address.toInt = base + offset
  loaded : X86CodePlacement.Placed native base (view emission.bytes)
  reads : ∀ register ∈ live (values (.inl activation)),
    X86RegisterRefinement.lookup native (physical register) = some (values (.inr register))
  flags : BitVec 32
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false

variable {live : LiveMap} {activation : Nat} {finish : Word} {nodes : List Node}
variable {first tail : List Chunk} {emission : Emission}
variable (layout : Layout live activation finish nodes first tail emission)

theorem region_marker_names (finish : Word) (nodes : List Node) (cursor : Nat) :
    (markersAt cursor (region finish nodes)).map Prod.fst =
      (nodes.map Node.point ++ [finish]).map BitVec.toNat := by
  induction nodes generalizing cursor with
  | nil => rfl
  | cons node later ih =>
    have shape : region finish (node :: later) =
        .label node.point.toNat :: (node.body ++ region finish later) := by
      simp [region, sites, List.append_assoc]
    rw [shape, markersAt, body_markers, List.map_cons, ih]
    rfl

include layout in
theorem Layout.distinct_points : (nodes.map Node.point ++ [finish]).Nodup := by
  obtain ⟨markers, unique⟩ := labelsAt_exact 0 _ layout.labels layout.resolved
  rw [markers, code, markersAt_append, markersAt_append, List.map_append,
    List.map_append, region_marker_names] at unique
  exact List.Nodup.of_map BitVec.toNat unique.of_append_right.of_append_left

/-- Logical positions remain ordered even when adjacent labels share a native address. -/
def remainingPoints (nodes : List Node) (finish point : Word) : Nat :=
  let points := nodes.map Node.point ++ [finish]
  points.length - points.idxOf point

include layout in
theorem Layout.word_advances (site : WordSite) (member : Node.word site ∈ nodes) :
    remainingPoints nodes finish site.next < remainingPoints nodes finish site.point := by
  obtain ⟨earlier, later, pieces⟩ := List.mem_iff_append.mp member
  have valid : Valid live activation finish (earlier ++ Node.word site :: later) := by
    rw [← pieces]
    exact layout.valid
  have next : site.next = entryName finish later := (valid_at live activation finish earlier (.word site) later valid).2.1
  let prior := earlier.map Node.point
  let future := later.map Node.point ++ [finish]
  have ordered : nodes.map Node.point ++ [finish] = prior ++ site.point :: future := by
    rw [pieces]
    simp [prior, future, Node.point]
  have unique := layout.distinct_points
  rw [ordered] at unique
  have apart := List.disjoint_left.mp unique.disjoint
  have laterPoint : site.next ∈ future := by rw [next]; cases later <;> simp [future, entryName]
  have nextIndex : future.idxOf site.next = 0 := by rw [next]; cases later <;> simp [future, entryName]
  have pointFresh : site.point ∉ prior := fun seen => apart seen (by simp)
  have nextFresh : site.next ∉ prior := fun seen => apart seen (List.mem_cons_of_mem _ laterPoint)
  have unequal : site.point ≠ site.next := by
    intro equal
    exact (List.nodup_cons.mp unique.of_append_right).1 (by simpa only [equal] using laterPoint)
  simp only [remainingPoints, ordered]
  rw [List.idxOf_append_of_notMem pointFresh, List.idxOf_append_of_notMem nextFresh,
    List.idxOf_cons_self, List.idxOf_cons_ne _ unequal, nextIndex, List.length_append, List.length_cons]
  omega

theorem Layout.positions (node : Node) (leading remaining : List Chunk)
    (whole : code finish nodes first tail =
      leading ++ (.label node.point.toNat :: (node.body ++ (.label node.next.toNat :: remaining)))) :
    X86Assembler.lookup layout.labels node.point.toNat = some (width leading) ∧
      X86Assembler.lookup layout.labels node.next.toNat = some (width leading + width node.body) := by
  constructor
  · apply label_lookup 0 _ _ layout.resolved
    rw [whole,markersAt_append,Nat.zero_add,markersAt]
    exact List.mem_append_right _ List.mem_cons_self
  · apply label_lookup 0 _ _ layout.resolved
    rw [whole,markersAt_append,Nat.zero_add,markersAt,body_markers,markersAt]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem literal_window (labels : Labels) (leading remaining : List Chunk) (point next : Nat)
    (data : List Byte) (emission : Emission)
    (emitted : emitAt labels 0 (leading ++ (.label point :: .bytes data :: .label next :: remaining)) = some emission) :
    ∃ before after, before.length = width leading ∧ emission.bytes = before ++ (data ++ after) := by
  obtain ⟨left,right,firstEmitted,restEmitted,whole⟩ :=
    emitAt_split labels 0 leading (.label point :: .bytes data :: .label next :: remaining) emission emitted
  have length := (emitAt_correct labels 0 leading left firstEmitted).1
  have rest : emitAt labels (width leading) (.label point :: .bytes data :: .label next :: remaining) = some right := by
    simpa only [Nat.zero_add] using restEmitted
  change (emitAt labels (width leading + data.length) remaining).bind
    (fun after => some (Emission.mk (data ++ after.bytes) after.fixups)) = some right at rest
  cases later : emitAt labels (width leading + data.length) remaining with
  | none => simp [later] at rest
  | some after =>
    rw [later] at rest
    have same : right = ⟨data ++ after.bytes,after.fixups⟩ := Option.some.inj rest.symm
    exact ⟨left.bytes,after.bytes,by simpa only [Nat.zero_add] using length,
      by rw [whole,same]; rfl⟩

include layout in
theorem Layout.word_window (site : WordSite) (leading remaining : List Chunk)
    (whole : code finish nodes first tail =
      leading ++ (.label site.point.toNat :: ((Node.word site).body ++ (.label site.next.toNat :: remaining)))) :
    ∃ before after, before.length = width leading ∧
      emission.bytes = before ++ ((X86DataPrimitive.bytes site.instruction).map (BitVec.ofNat 8) ++ after) := by
  have emitted := layout.assembled
  unfold assemble at emitted
  rw [layout.resolved] at emitted
  change emitAt layout.labels 0 (code finish nodes first tail) = some emission at emitted
  rw [whole] at emitted
  exact literal_window layout.labels leading remaining site.point.toNat site.next.toNat _ emission emitted

theorem Layout.target_inside (values : Values) (offset : Nat)
    (named : X86Assembler.lookup layout.labels (values (.inl activation)).toNat = some offset) :
    offset ≤ emission.bytes.length := by
  have inside := labels_inside 0 _ layout.labels layout.resolved _
    (lookup_member layout.labels _ _ named)
  have length := (assemble_correct _ emission layout.assembled).1
  omega

def Ready.resume {base : Int} {values : Values} {native : State} (ready : Ready layout base values native)
    (following : Values) (after : State) (offset : Nat) (registers : Finset Register)
    (named : X86Assembler.lookup layout.labels (following (.inl activation)).toNat = some offset)
    (frame : RegisterFrame registers native after) (dataOnly : registers ⊆ dataRegisters)
    (pointer : after.regs.get? .rip = some ((address base offset).signExtend 64))
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags)
    (readbacks : ∀ register ∈ live (following (.inl activation)),
      X86RegisterRefinement.lookup after (physical register) = some (following (.inr register))) :
    Ready layout base following after := by
  have inside := layout.target_inside following offset named
  have position : (address base offset).toInt = base + offset :=
    address_toInt base ready.lower (by have := ready.upper; omega) offset inside
  let origin := X86StateFrame.basisAt native after ready.origin (X86StateFrame.registerOnly frame) dataOnly
    (address base offset) (by rw [position]; have := ready.upper; omega) pointer
  exact {
    origin := origin
    lower := ready.lower
    upper := ready.upper
    offset := offset
    control := named
    location := position
    loaded := by intro index byte present; rw [frame.memory]; exact ready.loaded index byte present
    reads := readbacks
    flags := flags
    flagsKnown := flagsKnown
    quiet := (frame.registers .log_register_writes
      (fun member => (by decide : .log_register_writes ∉ dataRegisters) (dataOnly member))).trans ready.quiet }

theorem Ready.pointer {base : Int} {values : Values} {native : State} (ready : Ready layout base values native) :
    native.regs.get? .rip = some ((address base ready.offset).signExtend 64) := by
  have actual : address base ready.offset = ready.origin.address := by
    unfold address
    rw [← ready.location]
    exact BitVec.ofInt_toInt
  rw [actual]
  exact ready.origin.rip

def Node.nextValues : Node → Values → Values
  | .word site, values => site.row.nextValues values
      (X86DataPrimitive.evaluate site.instruction (fun register => values (.inr register)))
  | .branch choice, values =>
      Function.update values (.inl choice.activation) (X86BranchCompiler.chosen choice (values (.inr choice.condition)))

theorem Node.source_point (node : Node) (values written : Values)
    (guarded : node.recipe.guard (node.recipe.inputs.map values) (node.recipe.outputs.map written) = true) :
    values (.inl node.activation) = node.point := by
  cases node with
  | word site => exact ((site.row.guard_iff values written).mp guarded).1
  | branch choice => exact ((choice.guard_iff values written).mp guarded).1

theorem Node.source_finish (node : Node) (values written : Values)
    (guarded : node.recipe.guard (node.recipe.inputs.map values) (node.recipe.outputs.map written) = true) :
    CellEffects.overwrite node.recipe.writes values written = node.nextValues values := by
  cases node with
  | word site =>
    obtain ⟨_current,next,computed⟩ := (site.row.guard_iff values written).mp guarded
    have correct := X86DataPrimitive.computes site.instruction (fun register => values (.inr register))
    have result : written (.inr (X86DataPrimitive.destination site.instruction)) =
        X86DataPrimitive.evaluate site.instruction (fun register => values (.inr register)) :=
      Option.some.inj (computed.symm.trans correct)
    exact site.row.overwrite_eq_nextValues values written next _ result
  | branch choice =>
    obtain ⟨_current,target⟩ := (choice.guard_iff values written).mp guarded
    have selected : written (.inl choice.activation) = X86BranchCompiler.chosen choice (values (.inr choice.condition)) := by
      rcases (choice.target?_iff _ _).mp target with ⟨zero,result⟩ | ⟨one,result⟩
      · have zero' : values (.inr choice.condition) = (0#64) := zero
        unfold X86BranchCompiler.chosen
        rw [if_pos zero']
        exact result
      · have nonzero : values (.inr choice.condition) ≠ (0#64) := by rw [one]; decide
        unfold X86BranchCompiler.chosen
        rw [if_neg nonzero]
        exact result
    exact (choice.overwrite_eq values written).trans (congrArg (Function.update values (.inl choice.activation)) selected)

theorem word_next_control (site : WordSite) (values : Values) (owner : site.activation = activation) :
    (Node.word site).nextValues values (.inl activation) = site.next := by
  simp [Node.nextValues,Control.Row.nextValues,WordSite.row,owner]

include layout in
theorem Layout.elision_decreases (node : Node) (member : node ∈ nodes) (values : Values)
    (current : values (.inl activation) = node.point) (elided : node.count = 0) :
    remainingPoints nodes finish (node.nextValues values (.inl activation)) <
      remainingPoints nodes finish (values (.inl activation)) := by
  cases node with
  | word site =>
    rw [word_next_control site values (layout.site (.word site) member).1, current]
    exact layout.word_advances site member
  | branch choice => simp [Node.count] at elided

theorem word_next_register (site : WordSite) (values : Values) (register : Key) :
    (Node.word site).nextValues values (.inr register) =
      if register = X86DataPrimitive.destination site.instruction then
        X86DataPrimitive.evaluate site.instruction (fun register => values (.inr register))
      else values (.inr register) := by
  change (Function.update (Function.update values (.inl site.activation) site.next)
    (.inr (X86DataPrimitive.destination site.instruction))
    (X86DataPrimitive.evaluate site.instruction (fun register => values (.inr register)))) (.inr register) = _
  by_cases same : register = X86DataPrimitive.destination site.instruction
  · rw [if_pos same,congrArg Sum.inr same,Function.update_self]
  · rw [if_neg same,Function.update_of_ne (by intro equal; exact same (Sum.inr.inj equal)),
      Function.update_of_ne (by simp)]

theorem word_loaded {base : Int} {values : Values} {native : State} (ready : Ready layout base values native)
    (site : WordSite) (leading remaining : List Chunk)
    (whole : code finish nodes first tail =
      leading ++ (.label site.point.toNat :: ((Node.word site).body ++ (.label site.next.toNat :: remaining))))
    (position : ready.origin.address.toInt = base + width leading) :
    codeLoaded native ready.origin.address.toInt (X86DataPrimitive.bytes site.instruction) ∧
      ready.origin.address.toInt + (X86DataPrimitive.bytes site.instruction).length + 3 < (2 ^ 47 : Int) := by
  obtain ⟨before,after,length,image⟩ := layout.word_window site leading remaining whole
  have lengths := congrArg List.length image
  simp only [List.length_append,List.length_map,length] at lengths
  refine ⟨?_,by rw [position]; have := ready.upper; omega⟩
  intro index byte present
  have within := (List.getElem?_eq_some_iff.mp present).1
  have found : emission.bytes[width leading + index]? = some (BitVec.ofNat 8 byte) := by
    rw [image,List.getElem?_append_right (by omega),length,Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa only [List.length_map] using within),List.getElem?_map,present]
    rfl
  have shifted : address base (width leading + index) = address ready.origin.address.toInt index := by
    rw [position]
    simp only [address,Int.natCast_add,Int.add_assoc]
  simpa only [shifted] using ready.loaded _ _ found

theorem word_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (site : WordSite) (member : Node.word site ∈ nodes) (values : Values) (native : State)
    (ready : Ready layout base values native) (current : values (.inl activation) = site.point) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ _next : Ready layout base ((Node.word site).nextValues values) after,
      (X86FuelPrefix.fetches (X86DataPrimitive.count site.instruction)).run native = .ok () after ∧
      RegisterFrame (X86DataPrimitive.writes site.instruction) native after ∧
      X86ControlFlags.Preserved native after ∧
      (∀ count ≤ X86DataPrimitive.count site.instruction, ∀ observed,
        (X86FuelPrefix.fetches count).run native = .ok () observed →
          RegisterFrame (X86DataPrimitive.writes site.instruction) native observed) ∧
      X86WordPrimitive.StrictPrefixesIn (base + ready.offset) (width (Node.word site).body)
        (X86DataPrimitive.count site.instruction) native := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨owner,liveOK,leading,remaining,whole⟩ := layout.site (.word site) member
  have owner' : site.activation = activation := owner
  have liveOK' : (X86DataPrimitive.effect site.instruction).inputs.toFinset ⊆ live site.point ∧
      live site.next ⊆ insert (X86DataPrimitive.destination site.instruction) (live site.point) := liveOK
  obtain ⟨point,nextPoint⟩ := layout.positions (.word site) leading remaining whole
  have sameOffset : ready.offset = width leading := by
    have control := ready.control
    rw [current] at control
    exact Option.some.inj (control.symm.trans point)
  have position : ready.origin.address.toInt = base + width leading := by rw [← sameOffset]; exact ready.location
  obtain ⟨loaded,upper⟩ := word_loaded layout ready site leading remaining whole position
  have known : ∀ register ∈ (X86DataPrimitive.effect site.instruction).inputs,
      X86RegisterRefinement.lookup native (physical register) = some (values (.inr register)) := by
    intro register present
    apply ready.reads register
    rw [current]
    exact liveOK'.1 (List.mem_toFinset.mpr present)
  obtain ⟨after,flags,run,frame,result,pointer,flagsKnown,_quiet,control,prefixes,positions⟩ :=
    X86DataPrimitive.executes_with_prefix_addresses other extra vector site.instruction
      (fun register => values (.inr register)) native ready.origin known ready.flags ready.flagsKnown ready.quiet upper loaded
  have widthBody : width (Node.word site).body = (X86DataPrimitive.bytes site.instruction).length := by
    simp [Node.body,width,Chunk.width]
  have followingPoint : (Node.word site).nextValues values (.inl activation) = site.next :=
    word_next_control site values owner'
  have named : X86Assembler.lookup layout.labels ((Node.word site).nextValues values (.inl activation)).toNat =
      some (width leading + width (Node.word site).body) := by rw [followingPoint]; exact nextPoint
  have addressEq : address ready.origin.address.toInt (X86DataPrimitive.bytes site.instruction).length =
      address base (width leading + width (Node.word site).body) := by
    rw [position,widthBody]
    simp only [address,Int.natCast_add,Int.add_assoc]
  rw [addressEq] at pointer
  have readbacks : ∀ register ∈ live ((Node.word site).nextValues values (.inl activation)),
      X86RegisterRefinement.lookup after (physical register) = some ((Node.word site).nextValues values (.inr register)) := by
    intro register present
    rw [followingPoint] at present
    by_cases selected : register = X86DataPrimitive.destination site.instruction
    · subst register
      simpa only [word_next_register,if_pos rfl,ite_true] using result
    · have oldLive : register ∈ live site.point :=
        (Finset.mem_insert.mp (liveOK'.2 present)).resolve_left selected
      rw [frame.lookup _ (X86DataPrimitive.other_logical site.instruction register selected),
        word_next_register,if_neg selected]
      apply ready.reads register
      rw [current]
      exact oldLive
  refine ⟨after,Ready.resume layout ready _ after _ _ named frame (X86DataPrimitive.writes_data _) pointer
    flags flagsKnown readbacks,run,frame,control,prefixes,?_⟩
  rw [widthBody,sameOffset,← position]
  exact positions

theorem branch_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (choice : Control.Branch Key) (member : Node.branch choice ∈ nodes)
    (keys : Finset Location) (included : choice.recipe.support ⊆ keys) (values : Values) (native : State)
    (ready : Ready layout base values native) (current : values (.inl activation) = choice.point)
    (canonical : values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ _next : Ready layout base ((Node.branch choice).nextValues values) after,
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ X86ControlFlags.Preserved native after ∧
      (∀ count ≤ 2, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame X86BranchGate.writes native observed) ∧
      X86WordPrimitive.StrictPrefixesIn (base + ready.offset) (width (Node.branch choice).body) 2 native := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨owner,liveOK,leading,remaining,whole⟩ := layout.site (.branch choice) member
  have owner' : choice.activation = activation := owner
  have liveOK' : choice.condition ∈ live choice.point ∧
      live choice.yes ⊆ live choice.point ∧ live choice.no ⊆ live choice.point := liveOK
  have whole' : code finish nodes first tail =
      leading ++ (X86BranchCompiler.lower choice (physical choice.condition) ++ remaining) := by
    simpa only [Node.point,Node.next,Node.body,X86BranchCompiler.lower,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using whole
  have assembled : assemble (leading ++ (X86BranchCompiler.lower choice (physical choice.condition) ++ remaining)) = some emission := by
    rw [← whole']
    exact layout.assembled
  obtain ⟨compiled⟩ := X86BranchCompiler.ofAssembly choice (physical choice.condition) leading remaining emission assembled
  have sameLabels : compiled.labels = layout.labels := by
    have resolved := layout.resolved
    rw [whole'] at resolved
    exact Option.some.inj (compiled.resolved.symm.trans resolved)
  have sameOffset : ready.offset = width leading := by
    have point := ready.control
    rw [current,← sameLabels] at point
    exact Option.some.inj (point.symm.trans compiled.point)
  let entry : X86BranchCompiler.Entry (physical choice.condition) (width leading) emission native := {
    base := base
    origin := ready.origin
    lower := ready.lower
    upper := ready.upper
    location := by rw [← sameOffset]; exact ready.location
    loaded := ready.loaded
    value := values (.inr choice.condition)
    known := ready.reads choice.condition (by rw [current]; exact liveOK'.1)
    flags := ready.flags
    flagsKnown := ready.flagsKnown
    quiet := ready.quiet }
  obtain ⟨after,correct⟩ := X86BranchCompiler.realizes_compiled (X86Shift.linkedHandlers other) extra vector choice (physical choice.condition)
    leading remaining emission compiled native entry keys values included (by rw [owner']; exact current) rfl canonical
  have followingPoint : (Node.branch choice).nextValues values (.inl activation) =
      X86BranchCompiler.chosen choice (values (.inr choice.condition)) := by
    simp only [Node.nextValues,owner',Function.update_self]
  have named : X86Assembler.lookup layout.labels ((Node.branch choice).nextValues values (.inl activation)).toNat =
      some (X86BranchCompiler.chosenOffset compiled entry.value) := by
    rw [followingPoint,← sameLabels]
    exact correct.outputLabel
  have readbacks : ∀ register ∈ live ((Node.branch choice).nextValues values (.inl activation)),
      X86RegisterRefinement.lookup after (physical register) = some ((Node.branch choice).nextValues values (.inr register)) := by
    intro register present
    rw [followingPoint] at present
    have oldLive : register ∈ live choice.point := by
      unfold X86BranchCompiler.chosen at present
      split at present
      · exact liveOK'.2.2 present
      · exact liveOK'.2.1 present
    rw [correct.frame.lookup _ (by generalize physical register = target; fin_cases target <;> decide)]
    simpa only [Node.nextValues,Function.update_of_ne (by simp : (Sum.inr register : Location) ≠ .inl choice.activation)]
      using ready.reads register (by rw [current]; exact oldLive)
  obtain ⟨flags,flagsKnown⟩ := correct.flags
  refine ⟨after,Ready.resume layout ready _ after _ _ named correct.frame X86BranchGate.writes_data
    correct.pointer flags flagsKnown readbacks,correct.run,correct.frame,correct.control,correct.prefixes,?_⟩
  intro count shorter observed run
  have bound : count ≤ 1 := by omega
  have location : ready.origin.address.toInt = base + ready.offset := ready.location
  interval_cases count
  · have same := X86FuelPrefix.fetches_deterministic 0 native native observed
      (X86FuelPrefix.fetches_zero native) run
    subst observed
    exact ⟨0,by change 0 < 9; decide,by simpa [address,← location] using ready.origin.rip⟩
  · let input := X86BranchCompiler.nativeInput choice (physical choice.condition) leading remaining emission
      compiled native entry.base entry.origin entry.lower entry.upper entry.location entry.loaded entry.value
      entry.known entry.flags entry.flagsKnown entry.quiet
    obtain ⟨tested,_,test,_,_,_,rip⟩ :=
      X86BranchGate.test_step (X86Shift.linkedHandlers other) extra vector native (physical choice.condition) input
    have same := X86FuelPrefix.fetches_deterministic 1 native tested observed
      (X86FuelPrefix.fetches_one _ _ test) run
    subst observed
    refine ⟨3,by change 3 < 9; decide,?_⟩
    change tested.regs.get? .rip = some ((address ready.origin.address.toInt 3).signExtend 64) at rip
    simpa only [location] using rip

theorem realizes_selected (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (node : Node) (member : node ∈ nodes) (values written : Values) (native : State)
    (ready : Ready layout base values native) (keys : Finset Location)
    (included : node.recipe.support ⊆ keys)
    (guarded : node.recipe.guard (node.recipe.inputs.map values) (node.recipe.outputs.map written) = true) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ _next : Ready layout base (node.nextValues values) after,
      (CellEffects.profile (nodes.map Node.recipe)).theory.rewrites (Cells.encode keys values)
        (Cells.encode keys (node.nextValues values)) ∧
      (X86FuelPrefix.fetches node.count).run native = .ok () after ∧
      RegisterFrame node.writes native after ∧ X86ControlFlags.Preserved native after ∧
      (∀ count ≤ node.count, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame node.writes native observed) ∧
      X86WordPrimitive.StrictPrefixesIn (base + ready.offset) (width node.body) node.count native := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  have owner := (layout.site node member).1
  have current : values (.inl activation) = node.point := by rw [← owner]; exact node.source_point values written guarded
  have source : (CellEffects.profile (nodes.map Node.recipe)).theory.rewrites (Cells.encode keys values)
      (Cells.encode keys (node.nextValues values)) := by
    apply (CellEffects.profile_rewrite_iff (nodes.map Node.recipe) keys values _).mpr
    exact ⟨node.recipe,List.mem_map.mpr ⟨node,member,rfl⟩,written,included,guarded,
      congrArg (Cells.encode keys) (node.source_finish values written guarded).symm⟩
  cases node with
  | word site =>
    obtain ⟨after,next,run,frame,control,prefixes,positions⟩ :=
      word_executes layout other extra vector site member values native ready current
    exact ⟨after,next,source,run,frame,control,prefixes,positions⟩
  | branch choice =>
    have target := ((choice.guard_iff values written).mp guarded).2
    have canonical := ((choice.target?_iff _ _).mp target).imp And.left And.left
    obtain ⟨after,next,run,frame,control,prefixes,positions⟩ :=
      branch_executes layout other extra vector choice member keys included values native ready current canonical
    exact ⟨after,next,source,run,frame,control,prefixes,positions⟩

/-- Actual resource firings with their selected template's instruction receipt. -/
def Counted (nodes : List Node) (before after : World × Nat) : Prop :=
  ∃ node ∈ nodes, ∃ invocation : CellEffects.Invocation node.recipe,
    CellEffects.system.Enables before.1 invocation ∧
      CellEffects.system.fire before.1 invocation = after.1 ∧ after.2 = before.2 + node.count

theorem source_selected_iff (nodes : List Node) (before following : World) :
    (CellEffects.profile (nodes.map Node.recipe)).theory.rewrites before following ↔
      ∃ node ∈ nodes, ∃ invocation : CellEffects.Invocation node.recipe,
        CellEffects.system.Enables before invocation ∧ CellEffects.system.fire before invocation = following := by
  have select : ∀ recipes : List (CellEffects.Recipe Location),
      (CellEffects.profile recipes).theory.rewrites before following ↔
        ∃ recipe ∈ recipes, ∃ invocation : CellEffects.Invocation recipe,
          CellEffects.system.Enables before invocation ∧ CellEffects.system.fire before invocation = following := by
    intro recipes
    constructor
    · rintro ⟨index,invocation,enabled,endpoint⟩
      exact ⟨recipes[index.down],List.getElem_mem index.down.isLt,invocation,enabled,endpoint.symm⟩
    · rintro ⟨recipe,member,invocation,enabled,endpoint⟩
      obtain ⟨index,rfl⟩ := List.mem_iff_get.mp member
      exact ⟨ULift.up index,invocation,enabled,endpoint.symm⟩
  refine (select (nodes.map Node.recipe)).trans ?_
  constructor
  · rintro ⟨recipe,member,invocation,enabled,endpoint⟩
    obtain ⟨node,present,rfl⟩ := List.mem_map.mp member
    exact ⟨node,present,invocation,enabled,endpoint⟩
  · rintro ⟨node,present,invocation,enabled,endpoint⟩
    exact ⟨node.recipe,List.mem_map.mpr ⟨node,present,rfl⟩,invocation,enabled,endpoint⟩

theorem counted_iff (nodes : List Node) (before following : World) (used : Nat) :
    (CellEffects.profile (nodes.map Node.recipe)).theory.rewrites before following ↔
      ∃ count, Counted nodes (before,used) (following,used + count) := by
  constructor
  · intro source
    obtain ⟨node,member,invocation,enabled,endpoint⟩ := (source_selected_iff nodes before following).mp source
    exact ⟨node.count,node,member,invocation,enabled,endpoint,rfl⟩
  · rintro ⟨_count,node,member,invocation,enabled,endpoint,_charged⟩
    exact (source_selected_iff nodes before following).mpr ⟨node,member,invocation,enabled,endpoint⟩

theorem counted_lift (nodes : List Node) {before following : World}
    (source : (CellEffects.profile (nodes.map Node.recipe)).theory.MultiStep before following) (used : Nat) :
    ∃ total, Relation.ReflTransGen (Counted nodes) (before,used) (following,total) := by
  have path : Relation.ReflTransGen (CellEffects.profile (nodes.map Node.recipe)).theory.rewrites before following :=
    (Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen
      (CellEffects.profile (nodes.map Node.recipe)).theory before following).mp source
  clear source
  induction path with
  | refl => exact ⟨used,Relation.ReflTransGen.refl⟩
  | @tail middle after _prior lastStep ih =>
    obtain ⟨middleUsed,prior⟩ := ih
    obtain ⟨count,last⟩ := (counted_iff nodes middle after middleUsed).mp lastStep
    exact ⟨middleUsed + count,prior.tail last⟩

theorem counted_erase (nodes : List Node) {before following : World × Nat}
    (source : Relation.ReflTransGen (Counted nodes) before following) :
    (CellEffects.profile (nodes.map Node.recipe)).theory.MultiStep before.1 following.1 := by
  induction source with
  | refl => exact .refl _
  | @tail middle after _path step ih =>
    obtain ⟨node,member,invocation,enabled,endpoint,_charged⟩ := step
    have single := (source_selected_iff nodes middle.1 after.1).mpr ⟨node,member,invocation,enabled,endpoint⟩
    exact Mettapedia.GSLT.Meredith.multiStep_trans _ ih (.step single (.refl _))

theorem counted_realized (nodes : List Node) (node : Node) (member : node ∈ nodes)
    (keys : Finset Location) (values written : Values) (used : Nat)
    (included : node.recipe.support ⊆ keys)
    (guarded : node.recipe.guard (node.recipe.inputs.map values) (node.recipe.outputs.map written) = true) :
    Counted nodes (Cells.encode keys values,used) (Cells.encode keys (node.nextValues values),used + node.count) := by
  obtain ⟨invocation,enabled,fire⟩ := CellEffects.effect_realized node.recipe keys values written included guarded
  exact ⟨node,member,invocation,enabled,
    fire.trans (congrArg (Cells.encode keys) (node.source_finish values written guarded)),rfl⟩

/-- The next valuation supplies precisely the outputs required by the current row. -/
theorem Node.next_guard (node : Node) (values : Values)
    (current : values (.inl node.activation) = node.point)
    (canonical : ∀ choice, node = .branch choice →
      values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) :
    node.recipe.guard (node.recipe.inputs.map values)
      (node.recipe.outputs.map (node.nextValues values)) = true := by
  cases node with
  | word site =>
    exact site.row.nextValues_guard values _ current
      (X86DataPrimitive.computes site.instruction (fun register => values (.inr register)))
  | branch choice =>
    apply (choice.guard_iff values _).mpr
    refine ⟨current,(choice.target?_iff _ _).mpr ?_⟩
    rcases canonical choice rfl with zero | one
    · exact Or.inl ⟨zero, by simp [Node.nextValues,X86BranchCompiler.chosen,zero]⟩
    · exact Or.inr ⟨one, by simp [Node.nextValues,X86BranchCompiler.chosen,one]⟩

/-- Select the source firing by the admitted control point and execute its emitted template. -/
theorem advance (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (node : Node) (member : node ∈ nodes) (keys : Finset Location)
    (values : Values) (native : State) (ready : Ready layout base values native) (used : Nat)
    (included : node.recipe.support ⊆ keys) (current : values (.inl activation) = node.point)
    (canonical : ∀ choice, node = .branch choice →
      values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ _next : Ready layout base (node.nextValues values) after,
      Counted nodes (Cells.encode keys values,used) (Cells.encode keys (node.nextValues values),used + node.count) ∧
      (X86FuelPrefix.fetches node.count).run native = .ok () after ∧
      RegisterFrame node.writes native after ∧ X86ControlFlags.Preserved native after ∧
      (∀ count ≤ node.count, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame node.writes native observed) ∧
      X86WordPrimitive.StrictPrefixesIn (base + ready.offset) (width node.body) node.count native := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  have guarded := node.next_guard values (by rw [(layout.site node member).1]; exact current) canonical
  obtain ⟨after,next,_,run,frame,control,prefixes,positions⟩ :=
    realizes_selected layout other extra vector node member values (node.nextValues values) native ready keys included guarded
  exact ⟨after,next,counted_realized nodes node member keys values _ used included guarded,run,frame,control,prefixes,positions⟩

/-- A completed native template recovers a source firing, including a zero-byte elision. -/
theorem reflect_native_node (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (node : Node) (member : node ∈ nodes) (keys : Finset Location)
    (values : Values) (native observed : State) (ready : Ready layout base values native) (used : Nat)
    (included : node.recipe.support ⊆ keys) (current : values (.inl activation) = node.point)
    (canonical : ∀ choice, node = .branch choice →
      values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1)
    (run : letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches node.count).run native = .ok () observed) :
    ∃ _next : Ready layout base (node.nextValues values) observed,
      Counted nodes (Cells.encode keys values,used) (Cells.encode keys (node.nextValues values),used + node.count) ∧
      RegisterFrame node.writes native observed ∧ X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,next,source,executed,frame,control,_⟩ :=
    advance layout other extra vector node member keys values native ready used included current canonical
  have equal := X86FuelPrefix.fetches_deterministic node.count native after observed executed run
  subst observed
  exact ⟨next,source,frame,control⟩

/-- Reflect a fetched prefix through whole templates and any zero-byte source steps.
At a declared exit the remaining fetches belong to the caller. Otherwise the
observed state is within the next template and that partial run has its frame. -/
theorem reflect_native_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {base : Int} (exits : List Word) (keys : Finset Location)
    (admitted : Values → Prop)
    (entry : ∀ values, admitted values → values (.inl activation) ∉ exits →
      ∃ node ∈ nodes, values (.inl activation) = node.point ∧
        (∀ choice, node = .branch choice →
          values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) ∧
        admitted (node.nextValues values))
    (resources : ∀ node ∈ nodes, node.recipe.support ⊆ keys)
    (values : Values) (native observed : State) (ready : Ready layout base values native)
    (wellFormed : admitted values) (used fuel : Nat)
    (run : letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches fuel).run native = .ok () observed) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ spent following boundary, ∃ next : Ready layout base following boundary,
      spent ≤ fuel ∧ admitted following ∧
      Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
        (Cells.encode keys following,used + spent) ∧
      (X86FuelPrefix.fetches spent).run native = .ok () boundary ∧
      RegisterFrame (footprint nodes) native boundary ∧ X86ControlFlags.Preserved native boundary ∧
      (∀ count ≤ spent, ∀ state, (X86FuelPrefix.fetches count).run native = .ok () state →
        RegisterFrame (footprint nodes) native state) ∧
      ((following (.inl activation) ∈ exits ∧ X86BranchGraph.AtExit layout.labels base exits boundary) ∨
        (following (.inl activation) ∉ exits ∧ ∃ node ∈ nodes,
          following (.inl activation) = node.point ∧ fuel - spent < node.count ∧
          (X86FuelPrefix.fetches (fuel - spent)).run boundary = .ok () observed ∧
          RegisterFrame node.writes boundary observed ∧ ∃ relative < width node.body,
            observed.regs.get? .rip = some ((address base (next.offset + relative)).signExtend 64))) := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases atExit : values (.inl activation) ∈ exits
  · exact ⟨0,values,native,ready,Nat.zero_le _,wellFormed,.refl,X86FuelPrefix.fetches_zero native,
      RegisterFrame.refl _ _,X86ControlFlags.Preserved.refl _,X86WordPrimitive.zero_prefixes native (footprint nodes),
      Or.inl ⟨atExit,_,atExit,ready.offset,ready.control,Ready.pointer layout ready⟩⟩
  obtain ⟨node,member,current,canonical,nextAdmitted⟩ := entry values wellFormed atExit
  obtain ⟨after,next,step,stepRun,stepFrame,stepFlags,stepPrefixes,positions⟩ :=
    advance layout other extra vector node member keys values native ready used (resources node member) current canonical
  by_cases insideBlock : fuel < node.count
  · obtain ⟨relative,inside,pointer⟩ := positions fuel insideBlock observed run
    have addressEq : address (base + ready.offset) relative = address base (ready.offset + relative) := by
      simp only [address,Int.natCast_add,Int.add_assoc]
    rw [addressEq] at pointer
    exact ⟨0,values,native,ready,Nat.zero_le _,wellFormed,.refl,X86FuelPrefix.fetches_zero native,
      RegisterFrame.refl _ _,X86ControlFlags.Preserved.refl _,X86WordPrimitive.zero_prefixes native (footprint nodes),
      Or.inr ⟨atExit,node,member,current,by simpa using insideBlock,by simpa using run,
        stepPrefixes fuel (Nat.le_of_lt insideBlock) observed run,relative,inside,pointer⟩⟩
  have addFuel : fuel = node.count + (fuel - node.count) := by omega
  obtain ⟨middle,headRun,tailRun⟩ := X86BlockCompiler.fetches_split node.count (fuel - node.count) native observed
    (addFuel ▸ run)
  have middleEq := X86FuelPrefix.fetches_deterministic node.count native after middle stepRun headRun
  subst middle
  obtain ⟨rest,following,boundary,resume,spends,nextOK,path,ran,frame,flags,prefixes,cut⟩ :=
    reflect_native_prefix other extra vector exits keys admitted entry resources (node.nextValues values) after observed
      next nextAdmitted (used + node.count) (fuel - node.count) tailRun
  have joinedPath : Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
      (Cells.encode keys following,used + (node.count + rest)) := by
    simpa only [Nat.add_assoc] using (Relation.ReflTransGen.single step).trans path
  have joinedRun := X86FuelPrefix.fetches_then node.count rest native after boundary stepRun ran
  have framed : RegisterFrame (footprint nodes) native after := stepFrame.mono (writes_in nodes node member)
  have headPrefixes : ∀ count ≤ node.count, ∀ state,
      (X86FuelPrefix.fetches count).run native = .ok () state → RegisterFrame (footprint nodes) native state :=
    fun count within state part => (stepPrefixes count within state part).mono (writes_in nodes node member)
  have allPrefixes := X86BranchGraph.prefixes_join (footprint nodes) node.count rest native after
    stepRun headPrefixes prefixes
  have left : fuel - (node.count + rest) = fuel - node.count - rest := by omega
  refine ⟨node.count + rest,following,boundary,resume,by omega,nextOK,joinedPath,joinedRun,
    (framed.trans frame).mono (by simp),stepFlags.trans flags,allPrefixes,?_⟩
  rw [left]
  exact cut
termination_by (fuel, remainingPoints nodes finish (values (.inl activation)))
decreasing_by
  by_cases elided : node.count = 0
  · rw [elided, Nat.sub_zero]
    exact Prod.Lex.right _ (layout.elision_decreases node member values current elided)
  · exact Prod.Lex.left _ _ (by omega)

theorem realizes_counted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (keys : Finset Location) (values : Values) (native : State) (ready : Ready layout base values native)
    (used : Nat) (target : World × Nat)
    (source : Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used) target) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ nextValues after, ∃ _next : Ready layout base nextValues after,
      used ≤ target.2 ∧ target.1 = Cells.encode keys nextValues ∧
      (X86FuelPrefix.fetches (target.2 - used)).run native = .ok () after ∧
      RegisterFrame (footprint nodes) native after ∧ X86ControlFlags.Preserved native after ∧
      ∀ count ≤ target.2 - used, ∀ observed,
        (X86FuelPrefix.fetches count).run native = .ok () observed → RegisterFrame (footprint nodes) native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  induction source with
  | refl =>
    refine ⟨values,native,ready,by omega,rfl,?_,RegisterFrame.refl _ _,X86ControlFlags.Preserved.refl native,?_⟩
    · simpa only [Nat.sub_self] using X86FuelPrefix.fetches_zero native
    · simpa only [Nat.sub_self] using X86WordPrimitive.zero_prefixes native (footprint nodes)
  | @tail middle following _prior lastStep ih =>
    obtain ⟨middleValues,middleNative,middleReady,monotone,middleEq,firstRun,firstFrame,firstControl,firstPrefixes⟩ := ih
    obtain ⟨node,member,invocation,enabled,endpoint,charged⟩ := lastStep
    have enabled' : CellEffects.system.Enables (Cells.encode keys middleValues) invocation := by
      rw [← middleEq]
      exact enabled
    have fire : CellEffects.system.fire (Cells.encode keys middleValues) invocation = following.1 := by
      rw [← middleEq]
      exact endpoint
    obtain ⟨included,_agree⟩ := (CellEffects.enabled_iff node.recipe invocation keys middleValues).mp enabled'
    have guarded := CellEffects.enabled_guard node.recipe invocation keys middleValues enabled'
    obtain ⟨after,next,_source,restRun,restFrame,restControl,restPrefixes,_positions⟩ :=
      realizes_selected layout other extra vector node member middleValues invocation.after middleNative middleReady keys included guarded
    have finalEq : following.1 = Cells.encode keys (node.nextValues middleValues) := by
      exact fire.symm.trans ((CellEffects.fire_refines_overwrite node.recipe invocation keys middleValues enabled').trans
        (congrArg (Cells.encode keys) (node.source_finish middleValues invocation.after guarded)))
    have countEq : (middle.2 - used) + node.count = following.2 - used := by omega
    have full := X86FuelPrefix.fetches_then (middle.2 - used) node.count native middleNative after firstRun restRun
    rw [countEq] at full
    have framed : RegisterFrame (footprint nodes) middleNative after := restFrame.mono (writes_in nodes node member)
    have prefixes : ∀ count ≤ node.count, ∀ observed,
        (X86FuelPrefix.fetches count).run middleNative = .ok () observed → RegisterFrame (footprint nodes) middleNative observed := by
      intro count within observed candidate
      exact (restPrefixes count within observed candidate).mono (writes_in nodes node member)
    have allPrefixes := X86BranchGraph.prefixes_join (footprint nodes) (middle.2 - used) node.count native middleNative
      firstRun firstPrefixes prefixes
    rw [countEq] at allPrefixes
    exact ⟨node.nextValues middleValues,after,next,by omega,finalEq,full,
      (firstFrame.trans framed).mono (by simp),firstControl.trans restControl,allPrefixes⟩

theorem realizes_multistep (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (keys : Finset Location) (values : Values) (native : State) (ready : Ready layout base values native)
    (following : World) (source : (CellEffects.profile (nodes.map Node.recipe)).theory.MultiStep (Cells.encode keys values) following) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ count nextValues after, ∃ _next : Ready layout base nextValues after,
      following = Cells.encode keys nextValues ∧
      (X86FuelPrefix.fetches count).run native = .ok () after ∧
      RegisterFrame (footprint nodes) native after ∧ X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (footprint nodes) native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨count,path⟩ := counted_lift nodes source 0
  obtain ⟨nextValues,after,next,_monotone,endpoint,run,frame,control,prefixes⟩ :=
    realizes_counted layout other extra vector keys values native ready 0 (following,count) path
  exact ⟨count,nextValues,after,next,endpoint,by simpa only [Nat.sub_zero] using run,
    frame,control,by simpa only [Nat.sub_zero] using prefixes⟩

theorem reflects_counted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {base : Int} (keys : Finset Location) (values : Values) (native observed : State) (ready : Ready layout base values native)
    (used : Nat) (target : World × Nat)
    (source : Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used) target)
    (candidate : letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (target.2 - used)).run native = .ok () observed) :
    ∃ nextValues, ∃ _next : Ready layout base nextValues observed,
      target.1 = Cells.encode keys nextValues ∧ RegisterFrame (footprint nodes) native observed ∧
      X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨nextValues,after,next,_monotone,endpoint,run,frame,control,_prefixes⟩ :=
    realizes_counted layout other extra vector keys values native ready used target source
  have same := X86FuelPrefix.fetches_deterministic (target.2 - used) native after observed run candidate
  subst observed
  exact ⟨nextValues,next,endpoint,frame,control⟩

/-- Zero-byte nodes may share an exit address. Interior nodes that execute
instructions start at addresses distinct from every declared exit. -/
def checkExitOffsets (labels : Labels) (nodes : List Node) (exits : List Word) : Bool :=
  X86BranchGraph.checkExitOffsets labels
    ((nodes.filter fun node => decide (0 < node.count ∧ node.point ∉ exits)).map Node.point) exits

/-- At an observed exit address, recover the logical exit by taking any
remaining elided source steps, with the same native state and receipt. -/
theorem settle_native_exit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {base : Int} (exits : List Word) (keys : Finset Location)
    (admitted : Values → Prop)
    (entry : ∀ values, admitted values → values (.inl activation) ∉ exits →
      ∃ node ∈ nodes, values (.inl activation) = node.point ∧
        (∀ choice, node = .branch choice →
          values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) ∧
        admitted (node.nextValues values))
    (resources : ∀ node ∈ nodes, node.recipe.support ⊆ keys)
    (checked : checkExitOffsets layout.labels nodes exits = true)
    (values : Values) (native : State) (ready : Ready layout base values native)
    (wellFormed : admitted values) (used : Nat)
    (observed : X86BranchGraph.AtExit layout.labels base exits native) :
    ∃ following, ∃ _next : Ready layout base following native,
      admitted following ∧ following (.inl activation) ∈ exits ∧
      Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
        (Cells.encode keys following,used) := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨spent,following,boundary,next,within,nextOK,path,run,_,_,_,cut⟩ :=
    reflect_native_prefix layout other extra vector exits keys admitted entry resources
      values native native ready wellFormed used 0 (X86FuelPrefix.fetches_zero native)
  have zero : spent = 0 := by omega
  subst spent
  have same := X86FuelPrefix.fetches_deterministic 0 native boundary native run
    (X86FuelPrefix.fetches_zero native)
  subst boundary
  rcases cut with ⟨logical,_⟩ | ⟨interior,node,member,current,remaining,_,_⟩
  · exact ⟨following,next,nextOK,logical,by simpa only [Nat.add_zero] using path⟩
  · exfalso
    have positive : 0 < node.count := by simpa using remaining
    have nonexit : node.point ∉ exits := by rwa [← current]
    have included : node.point ∈
        ((nodes.filter fun n => decide (0 < n.count ∧ n.point ∉ exits)).map Node.point) :=
      List.mem_map.mpr ⟨node,List.mem_filter.mpr ⟨member,by simp [positive,nonexit]⟩,rfl⟩
    obtain ⟨label,declared,offset,found,pointer⟩ := observed
    have bound : base + (emission.bytes.length : Int) < (2 ^ 47 : Int) := by
      have := next.upper
      omega
    have observedInside := layout.target_inside (fun _ => label) offset found
    have settledInside := layout.target_inside following next.offset next.control
    have addresses := congrArg BitVec.toInt
      (Option.some.inj ((Ready.pointer layout next).symm.trans pointer))
    rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64),
      BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64),
      address_toInt base next.lower bound next.offset settledInside,
      address_toInt base next.lower bound offset observedInside] at addresses
    have offsets : next.offset = offset := by omega
    unfold checkExitOffsets X86BranchGraph.checkExitOffsets at checked
    have rules := List.all_eq_true.mp checked label declared
    rw [found] at rules
    have different := List.all_eq_true.mp rules _ included
    rw [← current,next.control,offsets] at different
    simp at different

/-- Each declared native exit lies outside the byte span of every executing interior node. -/
def checkExitSpans (labels : Labels) (nodes : List Node) (exits : List Word) : Bool :=
  nodes.all fun node =>
    if 0 < node.count ∧ node.point ∉ exits then
      match X86Assembler.lookup labels node.point.toNat with
      | none => false
      | some start => exits.all fun target =>
        match X86Assembler.lookup labels target.toNat with
        | none => false
        | some stop => decide (stop < start ∨ start + width node.body ≤ stop)
    else true

theorem Layout.exit_outside_node {base : Int} (exits : List Word)
    (checked : checkExitSpans layout.labels nodes exits = true) (node : Node)
    (member : node ∈ nodes) (positive : 0 < node.count) (interior : node.point ∉ exits)
    (values : Values) (native observed : State) (ready : Ready layout base values native)
    (current : values (.inl activation) = node.point) (relative : Nat) (inside : relative < width node.body)
    (pointer : observed.regs.get? .rip = some ((address base (ready.offset + relative)).signExtend 64)) :
    ¬ X86BranchGraph.AtExit layout.labels base exits observed := by
  intro exit
  obtain ⟨label,declared,offset,found,exitPointer⟩ := exit
  have start : X86Assembler.lookup layout.labels node.point.toNat = some ready.offset := by
    rw [← current]
    exact ready.control
  unfold checkExitSpans at checked
  have separated := List.all_eq_true.mp checked node member
  simp only [if_pos (And.intro positive interior),start] at separated
  have forbidden := List.all_eq_true.mp separated label declared
  rw [found,decide_eq_true_eq] at forbidden
  obtain ⟨_,_,leading,remaining,whole⟩ := layout.site node member
  obtain ⟨firstLabel,nextLabel⟩ := layout.positions node leading remaining whole
  have sameStart : ready.offset = width leading := Option.some.inj (start.symm.trans firstLabel)
  have bodyEnd := layout.target_inside (fun _ => node.next) _ nextLabel
  have within : ready.offset + relative ≤ emission.bytes.length := by omega
  have exitWithin := layout.target_inside (fun _ => label) offset found
  have upper : base + (emission.bytes.length : Int) < (2 ^ 47 : Int) := by
    have := ready.upper
    omega
  have equal := congrArg BitVec.toInt (Option.some.inj (pointer.symm.trans exitPointer))
  rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64),
    BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64),
    address_toInt base ready.lower upper _ within,
    address_toInt base ready.lower upper _ exitWithin] at equal
  omega

/-- Recover the source path of a native run stopped at its first declared exit. -/
theorem reflect_native_exit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {base : Int} (exits : List Word) (keys : Finset Location)
    (admitted : Values → Prop)
    (entry : ∀ values, admitted values → values (.inl activation) ∉ exits →
      ∃ node ∈ nodes, values (.inl activation) = node.point ∧
        (∀ choice, node = .branch choice →
          values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) ∧
        admitted (node.nextValues values))
    (resources : ∀ node ∈ nodes, node.recipe.support ⊆ keys)
    (checked : checkExitSpans layout.labels nodes exits = true)
    (values : Values) (native observed : State) (ready : Ready layout base values native)
    (wellFormed : admitted values) (used fuel : Nat)
    (run : letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches fuel).run native = .ok () observed)
    (atExit : X86BranchGraph.AtExit layout.labels base exits observed)
    (firstExit : letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
      letI : VectorOpcodeHandlers := vector
      ∀ count < fuel, ∀ state, (X86FuelPrefix.fetches count).run native = .ok () state →
        ¬ X86BranchGraph.AtExit layout.labels base exits state) :
    ∃ following, ∃ _next : Ready layout base following observed,
      admitted following ∧ following (.inl activation) ∈ exits ∧
      Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
        (Cells.encode keys following,used + fuel) ∧
      RegisterFrame (footprint nodes) native observed ∧ X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨spent,following,boundary,next,within,nextOK,path,boundaryRun,frame,flags,_,cut⟩ :=
    reflect_native_prefix layout other extra vector exits keys admitted entry resources
      values native observed ready wellFormed used fuel run
  rcases cut with ⟨logical,physical⟩ | ⟨interior,node,member,current,remaining,_,_,relative,inside,pointer⟩
  · have exactFuel : spent = fuel := by
      by_contra different
      exact firstExit spent (by omega) boundary boundaryRun physical
    subst spent
    have same := X86FuelPrefix.fetches_deterministic fuel native boundary observed boundaryRun run
    subst observed
    exact ⟨following,next,nextOK,logical,path,frame,flags⟩
  · have positive : 0 < node.count := by omega
    have nonexit : node.point ∉ exits := by rwa [← current]
    exact False.elim (layout.exit_outside_node exits checked node member positive nonexit following boundary observed
      next current relative inside pointer atExit)

#print axioms reflect_native_exit

private theorem observed_first_exit [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (labels : Labels) (base : Int) (exits : List Word) (native : State)
    (reachable : ∃ limit observed, (X86FuelPrefix.fetches limit).run native = .ok () observed ∧
      X86BranchGraph.AtExit labels base exits observed) :
    ∃ fuel observed, (X86FuelPrefix.fetches fuel).run native = .ok () observed ∧
      X86BranchGraph.AtExit labels base exits observed ∧
      (∀ count < fuel, ∀ state, (X86FuelPrefix.fetches count).run native = .ok () state →
        ¬ X86BranchGraph.AtExit labels base exits state) ∧
      (∀ limit observed, (X86FuelPrefix.fetches limit).run native = .ok () observed →
        X86BranchGraph.AtExit labels base exits observed → fuel ≤ limit) := by
  classical
  let fuel := Nat.find reachable
  obtain ⟨observed, run, atExit⟩ := Nat.find_spec reachable
  refine ⟨fuel, observed, run, atExit, ?_, ?_⟩
  · intro count earlier state earlierRun earlierExit
    exact Nat.find_min reachable earlier ⟨state, earlierRun, earlierExit⟩
  · intro limit state limitRun limitExit
    exact Nat.find_min' reachable ⟨state, limitRun, limitExit⟩

/-- A finite source derivation to an exit bounds the first observed native
exit. Its exact receipt and source derivation follow by reflection. -/
theorem first_exit_of_counted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {base : Int} (exits : List Word) (keys : Finset Location)
    (admitted : Values → Prop)
    (entry : ∀ values, admitted values → values (.inl activation) ∉ exits →
      ∃ node ∈ nodes, values (.inl activation) = node.point ∧
        (∀ choice, node = .branch choice →
          values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) ∧
        admitted (node.nextValues values))
    (resources : ∀ node ∈ nodes, node.recipe.support ⊆ keys)
    (checked : checkExitSpans layout.labels nodes exits = true)
    (values target : Values) (native : State) (ready : Ready layout base values native)
    (wellFormed : admitted values) (used bound : Nat)
    (controlCell : (Sum.inl activation : Location) ∈ keys)
    (targetExit : target (.inl activation) ∈ exits)
    (source : Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
      (Cells.encode keys target,used + bound)) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ fuel observed following, ∃ _next : Ready layout base following observed,
      fuel ≤ bound ∧ (X86FuelPrefix.fetches fuel).run native = .ok () observed ∧
      X86BranchGraph.AtExit layout.labels base exits observed ∧
      (∀ count < fuel, ∀ state, (X86FuelPrefix.fetches count).run native = .ok () state →
        ¬ X86BranchGraph.AtExit layout.labels base exits state) ∧
      admitted following ∧ following (.inl activation) ∈ exits ∧
      Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
        (Cells.encode keys following,used + fuel) ∧
      RegisterFrame (footprint nodes) native observed ∧ X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨targetValues, targetNative, targetReady, _, endpoint, runToTarget, _, _, _⟩ :=
    realizes_counted layout other extra vector keys values native ready used
      (Cells.encode keys target,used + bound) source
  have agree := ((Cells.encode_le_iff keys keys targetValues target).mp (le_of_eq endpoint.symm)).2
  have sourceExit : targetValues (.inl activation) ∈ exits := by
    rw [agree _ controlCell]
    exact targetExit
  have reachesExit : X86BranchGraph.AtExit layout.labels base exits targetNative :=
    ⟨targetValues (.inl activation), sourceExit, targetReady.offset, targetReady.control,
      Ready.pointer layout targetReady⟩
  have within : (X86FuelPrefix.fetches bound).run native = .ok () targetNative := by
    simpa only [Prod.snd, Nat.add_sub_cancel_left] using runToTarget
  obtain ⟨fuel, observed, run, atExit, first, minimal⟩ :=
    observed_first_exit layout.labels base exits native ⟨bound, targetNative, within, reachesExit⟩
  obtain ⟨following, next, valid, logical, trace, frame, flags⟩ :=
    reflect_native_exit layout other extra vector exits keys admitted entry resources checked
      values native observed ready wellFormed used fuel run atExit first
  exact ⟨fuel, observed, following, next, minimal bound targetNative within reachesExit,
    run, atExit, first, valid, logical, trace, frame, flags⟩

#print axioms first_exit_of_counted

/-- A source ranking supplies termination at the first observed native exit.
The returned receipt counts the fetched instructions through that exit. -/
theorem terminates_at_first_exit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {base : Int} (exits : List Word) (keys : Finset Location)
    (admitted : Values → Prop) (rank : Values → Nat)
    (progress : ∀ current, admitted current → current (.inl activation) ∉ exits →
      ∃ node ∈ nodes, current (.inl activation) = node.point ∧
        (∀ choice, node = .branch choice →
          current (.inr choice.condition) = 0 ∨ current (.inr choice.condition) = 1) ∧
        admitted (node.nextValues current) ∧ rank (node.nextValues current) < rank current)
    (resources : ∀ node ∈ nodes, node.recipe.support ⊆ keys)
    (checked : checkExitSpans layout.labels nodes exits = true)
    (values : Values) (native : State) (ready : Ready layout base values native)
    (wellFormed : admitted values) (used : Nat) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ fuel observed following, ∃ _next : Ready layout base following observed,
      (X86FuelPrefix.fetches fuel).run native = .ok () observed ∧
      X86BranchGraph.AtExit layout.labels base exits observed ∧
      (∀ count < fuel, ∀ state, (X86FuelPrefix.fetches count).run native = .ok () state →
        ¬ X86BranchGraph.AtExit layout.labels base exits state) ∧
      admitted following ∧ following (.inl activation) ∈ exits ∧
      Relation.ReflTransGen (Counted nodes) (Cells.encode keys values,used)
        (Cells.encode keys following,used + fuel) ∧
      RegisterFrame (footprint nodes) native observed ∧ X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  have entry : ∀ current, admitted current → current (.inl activation) ∉ exits →
      ∃ node ∈ nodes, current (.inl activation) = node.point ∧
        (∀ choice, node = .branch choice →
          current (.inr choice.condition) = 0 ∨ current (.inr choice.condition) = 1) ∧
        admitted (node.nextValues current) := by
    intro current valid interior
    obtain ⟨node, member, point, canonical, nextValid, _decrease⟩ := progress current valid interior
    exact ⟨node, member, point, canonical, nextValid⟩
  have reaches : ∀ (measure : Nat) (current : Values) (before : State),
      rank current = measure → Ready layout base current before → admitted current →
      ∃ fuel observed, (X86FuelPrefix.fetches fuel).run before = .ok () observed ∧
        X86BranchGraph.AtExit layout.labels base exits observed := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure smaller =>
      intro current before ranked readyBefore valid
      by_cases atEnd : current (.inl activation) ∈ exits
      · exact ⟨0, before, X86FuelPrefix.fetches_zero before,
          current (.inl activation), atEnd, readyBefore.offset, readyBefore.control,
          Ready.pointer layout readyBefore⟩
      · obtain ⟨node, member, point, canonical, nextValid, decrease⟩ := progress current valid atEnd
        obtain ⟨middle, next, _source, run, _frame, _flags, _prefix, _locations⟩ :=
          advance layout other extra vector node member keys current before readyBefore 0
            (resources node member) point canonical
        have below : rank (node.nextValues current) < measure := ranked ▸ decrease
        obtain ⟨tailFuel, observed, tailRun, atExit⟩ :=
          smaller _ below (node.nextValues current) middle rfl next nextValid
        exact ⟨node.count + tailFuel, observed,
          X86FuelPrefix.fetches_then node.count tailFuel before middle observed run tailRun, atExit⟩
  obtain ⟨fuel, observed, run, atExit, firstExit, _⟩ :=
    observed_first_exit layout.labels base exits native (reaches (rank values) values native rfl ready wellFormed)
  obtain ⟨following, next, valid, logicalExit, source, frame, flags⟩ :=
    reflect_native_exit layout other extra vector exits keys admitted entry resources checked
      values native observed ready wellFormed used fuel run atExit firstExit
  exact ⟨fuel, observed, following, next, run, atExit, firstExit, valid, logicalExit, source, frame, flags⟩

#print axioms terminates_at_first_exit

end Mettapedia.Machines.TIsa.X86MixedRegion
