theory Prop21
	imports n21helper ABCequalsCBA Geometry NCdistinct NChelper NCorder Prop16 Prop20 TTflip TTflip2 TTorder TTtransitive angleorderrespectscongruence angleorderrespectscongruence2 angleordertransitive betweennotequal collinearorder equalangleshelper equalanglesreflexive inequalitysymmetric ray4 ray5
begin

theorem(in euclidean_geometry) Prop21:
	assumes 
		"triangle A B C"
		"bet A E C"
		"bet B D E"
	shows "seg_sum_pair_gt B A A C B D D C \<and> ang_lt B A C B D C"
proof -
	have "bet E D B" using betweennesssymmetryE[OF `bet B D E`] .
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "col A E C" using collinear_b `bet A E C` by blast
	have "col A C E" using collinearorder[OF `col A E C`] by blast
	have "A \<noteq> E" using betweennotequal[OF `bet A E C`] by blast
	have "\<not> col A C B" using NCorder[OF `\<not> col A B C`] by blast
	have "A = A" using equalityreflexiveE.
	have "col A C A" using collinear_b `A = A` by blast
	have "\<not> col A E B" using NChelper[OF `\<not> col A C B` `col A C A` `col A C E` `A \<noteq> E`] .
	have "\<not> col A B E" using NCorder[OF `\<not> col A E B`] by blast
	have "triangle A B E" using triangle_b[OF `\<not> col A B E`] .
	have "seg_sum_gt B A A E B E" using Prop20[OF `triangle A B E`] .
	have "seg_sum_pair_gt B A A C B E E C" using n21helper[OF `seg_sum_gt B A A E B E` `bet A E C`] .
	have "\<not> col A C B" using NCorder[OF `\<not> col A B C`] by blast
	have "col A E C" using collinear_b `bet A E C` by blast
	have "col A C E" using collinearorder[OF `col A E C`] by blast
	have "C = C" using equalityreflexiveE.
	have "col A C C" using collinear_b `C = C` by blast
	have "E \<noteq> C" using betweennotequal[OF `bet A E C`] by blast
	have "\<not> col E C B" using NChelper[OF `\<not> col A C B` `col A C E` `col A C C` `E \<noteq> C`] .
	have "\<not> col E B C" using NCorder[OF `\<not> col E C B`] by blast
	have "col E D B" using collinear_b `bet E D B` by blast
	have "col E B D" using collinearorder[OF `col E D B`] by blast
	have "E = E" using equalityreflexiveE.
	have "col E B E" using collinear_b `E = E` by blast
	have "E \<noteq> D" using betweennotequal[OF `bet E D B`] by blast
	have "\<not> col E D C" using NChelper[OF `\<not> col E B C` `col E B E` `col E B D` `E \<noteq> D`] .
	have "\<not> col E C D" using NCorder[OF `\<not> col E D C`] by blast
	have "triangle E C D" using triangle_b[OF `\<not> col E C D`] .
	have "seg_sum_gt C E E D C D" using Prop20[OF `triangle E C D`] .
	have "seg_sum_pair_gt C E E B C D D B" using n21helper[OF `seg_sum_gt C E E D C D` `bet E D B`] .
	have "seg_sum_pair_gt E B C E C D D B" using TTorder[OF `seg_sum_pair_gt C E E B C D D B`] .
	have "seg_sum_pair_gt B E E C C D D B" using TTflip[OF `seg_sum_pair_gt E B C E C D D B`] .
	have "seg_sum_pair_gt B A A C C D D B" using TTtransitive[OF `seg_sum_pair_gt B A A C B E E C` `seg_sum_pair_gt B E E C C D D B`] .
	have "seg_sum_pair_gt B A A C B D D C" using TTflip2[OF `seg_sum_pair_gt B A A C C D D B`] .
	have "bet E D B" using `bet E D B` .
	have "\<not> col C E D" using NCorder[OF `\<not> col E C D`] by blast
	have "triangle C E D" using triangle_b[OF `\<not> col C E D`] .
	have "ang_lt D E C C D B" using Prop16[OF `triangle C E D` `bet E D B`] by blast
	have "\<not> col E B C" using NCorder[OF `\<not> col E C B`] by blast
	have "B = B" using equalityreflexiveE.
	have "col E B B" using collinear_b `B = B` by blast
	have "col E D B" using collinear_b `bet E D B` by blast
	have "col E B D" using collinearorder[OF `col E D B`] by blast
	have "B \<noteq> D" using betweennotequal[OF `bet B D E`] by blast
	have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
	have "\<not> col D B C" using NChelper[OF `\<not> col E B C` `col E B D` `col E B B` `D \<noteq> B`] .
	have "\<not> col B A E" using NCorder[OF `\<not> col A B E`] by blast
	have "triangle B A E" using triangle_b[OF `\<not> col B A E`] .
	have "ang_lt E A B B E C" using Prop16[OF `triangle B A E` `bet A E C`] by blast
	have "ang_eq B A E E A B" using ABCequalsCBA[OF `\<not> col B A E`] .
	have "ang_lt B A E B E C" using angleorderrespectscongruence2[OF `ang_lt E A B B E C` `ang_eq B A E E A B`] .
	have "\<not> col C E B" using NCorder[OF `\<not> col E B C`] by blast
	have "ang_eq C E B B E C" using ABCequalsCBA[OF `\<not> col C E B`] .
	have "ang_lt B A E C E B" using angleorderrespectscongruence[OF `ang_lt B A E B E C` `ang_eq C E B B E C`] .
	have "A \<noteq> E" using betweennotequal[OF `bet A E C`] by blast
	have "ray_on A E C" using ray4 `bet A E C` `A \<noteq> E` by blast
	have "ray_on A C E" using ray5[OF `ray_on A E C`] .
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "ray_on A B B" using ray4 `B = B` `A \<noteq> B` by blast
	have "\<not> col B A C" using NCorder[OF `\<not> col A B C`] by blast
	have "ang_eq B A C B A C" using equalanglesreflexive[OF `\<not> col B A C`] .
	have "ang_eq B A C B A E" using equalangleshelper[OF `ang_eq B A C B A C` `ray_on A B B` `ray_on A C E`] .
	have "bet E D B" using betweennesssymmetryE[OF `bet B D E`] .
	have "ray_on E D B" using ray4 `bet E D B` `E \<noteq> D` by blast
	have "C = C" using equalityreflexiveE.
	have "ray_on E C C" using ray4 `C = C` `E \<noteq> C` by blast
	have "\<not> col C E D" using NCorder[OF `\<not> col E C D`] by blast
	have "ang_eq C E D C E D" using equalanglesreflexive[OF `\<not> col C E D`] .
	have "ang_eq C E D C E B" using equalangleshelper[OF `ang_eq C E D C E D` `ray_on E C C` `ray_on E D B`] .
	have "ang_lt B A E C E D" using angleorderrespectscongruence[OF `ang_lt B A E C E B` `ang_eq C E D C E B`] .
	have "ang_lt B A C C E D" using angleorderrespectscongruence2[OF `ang_lt B A E C E D` `ang_eq B A C B A E`] .
	have "\<not> col D E C" using NCorder[OF `\<not> col C E D`] by blast
	have "ang_eq D E C C E D" using ABCequalsCBA[OF `\<not> col D E C`] .
	have "ang_lt B A C D E C" using angleorderrespectscongruence[OF `ang_lt B A C C E D` `ang_eq D E C C E D`] .
	have "ang_lt B A C C D B" using angleordertransitive[OF `ang_lt B A C D E C` `ang_lt D E C C D B`] .
	have "\<not> col B D C" using NCorder[OF `\<not> col D B C`] by blast
	have "ang_eq B D C C D B" using ABCequalsCBA[OF `\<not> col B D C`] .
	have "ang_lt B A C B D C" using angleorderrespectscongruence[OF `ang_lt B A C C D B` `ang_eq B D C C D B`] .
	have "seg_sum_pair_gt B A A C B D D C \<and> ang_lt B A C B D C" using `seg_sum_pair_gt B A A C B D D C` `ang_lt B A C B D C` by blast
	thus ?thesis by blast
qed

end