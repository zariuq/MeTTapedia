fof(c_Subq,axiom,(! [X0:$i] : (! [X1:$i] : (c_Subq(c_X0,c_X1) <=> (! [X2] : (c_In(X2,c_X0) => c_In(X2,c_X1))))))). % 8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87
fof(set_5Fext,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => (c_Subq(X1,X0) => (X0 = X1)))))). % 5189b0389a1efe35ba744aa1436bb23541e75e8a85658313375e1e0b3321128f
fof(c_EmptyAx,axiom,~ (? [X0] : c_In(X0,c_Empty))). % 920f955f033a1286fcaba96c8eb55d2079812a3041ff6b812df4cc2636156b59
fof(c_UnionEq,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Union(X0)) <=> (? [X2] : (c_In(X1,X2) & c_In(X2,X0))))))). % 0b67fbe4188c03468f8cd69c462ea8e5fb2269bf1fd67125a6456853d4ab7c74
fof(c_PowerEq,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Power(X0)) <=> c_Subq(X1,X0))))). % b492ab96942311595fd53c93243cb7ab5314986bb8460d580d9382dfab90f7d1
fof(c_TransSet,axiom,(! [X0:$i] : (c_TransSet(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_Subq(X1,c_X0)))))). % e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3
fof(c_Union_5Fclosed,axiom,(! [X0:$i] : (c_Union_5Fclosed(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_In(c_Union(X1),c_X0)))))). % 54850182033d0575e98bc2b12aa8b9baaa7a541e9d5abc7fddeb74fc5d0a19ac
fof(c_Power_5Fclosed,axiom,(! [X0:$i] : (c_Power_5Fclosed(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_In(c_Power(X1),c_X0)))))). % 5a811b601343da9ff9d05d188d672be567de94b980bbbe0e04e628d817f4c7ac
fof(c_ZF_5Fclosed,axiom,(! [X0:$i] : (c_ZF_5Fclosed(c_X0) <=> ((c_Union_5Fclosed(c_X0) & c_Power_5Fclosed(c_X0)) & c_Repl_5Fclosed(c_X0))))). % 43f34d6a2314b56cb12bf5cf84f271f3f02a3e68417b09404cc73152523dbfa0
fof(c_UnivOf_5FIn,axiom,(! [X0] : c_In(X0,c_UnivOf(X0)))). % 64ad93d240a001e91d619642c36f7ea8387780b9860b748f282d12bc22d4a677
fof(c_UnivOf_5FTransSet,axiom,(! [X0] : c_TransSet(c_UnivOf(X0)))). % 40723e6db0df4f3bce8b35ba709f46fd1f4a94f61bdd2e206b8d4e21ea660332
fof(c_UnivOf_5FZF_5Fclosed,axiom,(! [X0] : c_ZF_5Fclosed(c_UnivOf(X0)))). % 4181a4a1a92ac574d2c6208a18ed79b8773a8c1de9330f96e76e3edabcf083ea
fof(c_UnivOf_5FMin,axiom,(! [X0] : (! [X1] : (c_In(X0,X1) => (c_TransSet(X1) => (c_ZF_5Fclosed(X1) => c_Subq(c_UnivOf(X0),X1))))))). % 9a6fd4292d63e7be0caf7c85f8d8c56e3be3c23ff46c2001263cd459da21e6ed
fof(nIn,axiom,(! [X0:$i] : (! [X1:$i] : (nIn(c_X0,c_X1) <=> ~ c_In(c_X0,c_X1))))). % 2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359
fof(c_EmptyE,axiom,(! [X0] : nIn(X0,c_Empty))). % db69db5fe0ab30c62cbb6c6a5585580d13a89b7a739501bf6ab7f69ba07ed65e
fof(c_PowerI,axiom,(! [X0] : (! [X1] : (c_Subq(X1,X0) => c_In(X1,c_Power(X0)))))). % 8ec4fb130787ca0a60ebd05ea54a7a9f309a462585bcc1ee86952371bbf7d709
fof(c_Subq_5FEmpty,axiom,(! [X0] : c_Subq(c_Empty,X0))). % ec40ffd5e1efa2305904493e93693c9ded9ce1a6c83c767acc34b0a727c8c8ff
fof(c_Empty_5FIn_5FPower,axiom,(! [X0] : c_In(c_Empty,c_Power(X0)))). % 57bdeb692b87bc968dc5c4c76518265b349fad59aa9d410f1763da99db3af2d7
fof(eq_5Fi_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : ((X0 = X1) => ((X1 = X2) => (X0 = X2))))))). % ebaf3a176014e42e2f894150fb11347d641abecb9be82d29a784bb9b0312d2e8
fof(neq_5Fi_5Fsym,axiom,(! [X0] : (! [X1] : (~ (X0 = X1) => ~ (X1 = X0))))). % 5975ea0d667ef81890db1136e825d1bda7a0dec6bacfabb8f8c03bae6c9d6bde
fof(c_Subq_5Fref,axiom,(! [X0] : c_Subq(X0,X0))). % 8cc027a87882f9d68d5bb3a254ca44809bb1f7acc0d6ad2ed1d5aa7f040b3422
fof(c_Subq_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X0,X1) => (c_Subq(X1,X2) => c_Subq(X0,X2))))))). % 065e1c25434d58f32a87cf53ecf8bea2d3e1eb2dc3e022e6bd6f5e03e5f845a5
fof(c_Empty_5FSubq_5Feq,axiom,(! [X0] : (c_Subq(X0,c_Empty) => (X0 = c_Empty)))). % 3eadb639389a682a69e54b191ac296a25a1a39baabdefa25ba9bccbeb7038d35
fof(c_Empty_5Feq,axiom,(! [X0] : ((! [X1] : nIn(X1,X0)) => (X0 = c_Empty)))). % 4b1c3808883170ae2c35267bed4184182595364acf85a55cf81ba0b3c95c9de5
fof(c_UnionI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X1,X2) => (c_In(X2,X0) => c_In(X1,c_Union(X0)))))))). % 681f08928f47fe62e4803e6fa2b70b4ea7a5d093a6d00273519a068fea82736f
fof(c_UnionE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Union(X0)) => (? [X2] : (c_In(X1,X2) & c_In(X2,X0))))))). % 704291d62c629bb6d6fba75f33b0b13133e87259f1defdfafd1142825f56775c
fof(c_PowerE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Power(X0)) => c_Subq(X1,X0))))). % e6c5658300fbb425904a43da92acd1b8285eb12502cbe3e889df5f01952d03f8
fof(c_Self_5FIn_5FPower,axiom,(! [X0] : c_In(X0,c_Power(X0)))). % 9e7d17e9e24e10742a1db89c76f516cfd1d826d9141665d2cdfcc8973b143d8d
fof(conj_hammer_test_418,conjecture,(! [X0] : (! [X1] : (! [X2] : (c_In(X0,c_UPair(X1,X2)) => ((X0 = X1) | (X0 = X2))))))).
