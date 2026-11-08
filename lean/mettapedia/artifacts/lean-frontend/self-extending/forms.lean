namespace FormsStream
scoped syntax:65 (name := addS) term:65 " %%* " term:66 : term
#check 1 %%* 2 %%* 3
scoped notation:65 (name := addN) x:65 " %%~ " y:66 => Nat.add x y
#check 1 %%~ (2 %%* 3)
scoped syntax:80 (name := prefixS) " wave " term:81 : term
#check wave 2 %%* 3
end FormsStream
