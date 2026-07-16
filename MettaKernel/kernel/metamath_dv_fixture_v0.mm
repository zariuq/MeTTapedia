$( Test for DV pairwise expansion: $d x y z $. should create pair (y,z)
   This test REQUIRES (y,z) to be disjoint - will FAIL if pairwise expansion broken $)

$c wff |- $.
$v x y z $.

wx $f wff x $.
wy $f wff y $.
wz $f wff z $.

$( Key axiom: requires y and z to be disjoint $)
${
  $d y z $.
  ax-yz.1 $e |- y $.
  ax-yz $a |- z $.
$}

$( Theorem using multi-variable $d declaration
   The $d x y z $. MUST expand to include (y,z) for this to verify! $)
${
  $d x y z $.
  th.1 $e |- y $.
  th $p |- z $= wy wz th.1 ax-yz $.
$}
