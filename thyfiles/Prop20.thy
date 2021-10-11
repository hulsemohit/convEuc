theory Prop20
	imports ABCequalsCBA Geometry Prop05 Prop19 angleorderrespectscongruence angleorderrespectscongruence2 betweennotequal collinear4 collinearorder congruenceflip equalanglessymmetric equalanglestransitive inequalitysymmetric ray4
begin

theorem(in euclidean_geometry) Prop20:
	assumes 
		"triangle A B C"
	shows "seg_sum_gt B A A C B C"
proof -
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "col B A C" using collinear_b `B = A` by blast
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "\<not> (C = A)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> A)"
		hence "C = A" by blast
		have "col B C A" using collinear_b `C = A` by blast
		have "col A B C" using collinearorder[OF `col B C A`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "C \<noteq> A" by blast
	obtain D where "bet B A D \<and> seg_eq A D C A" using extensionE[OF `B \<noteq> A` `C \<noteq> A`]  by  blast
	have "bet B A D" using `bet B A D \<and> seg_eq A D C A` by blast
	have "A \<noteq> D" using betweennotequal[OF `bet B A D`] by blast
	have "D \<noteq> A" using inequalitysymmetric[OF `A \<noteq> D`] .
	have "B \<noteq> D" using betweennotequal[OF `bet B A D`] by blast
	have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
	have "seg_eq A D C A" using `bet B A D \<and> seg_eq A D C A` by blast
	have "seg_eq A D A C" using congruenceflip[OF `seg_eq A D C A`] by blast
	have "\<not> (col A D C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A D C))"
hence "col A D C" by blast
		have "col B A D" using collinear_b `bet B A D \<and> seg_eq A D C A` by blast
		have "col D A B" using collinearorder[OF `col B A D`] by blast
		have "col D A C" using collinearorder[OF `col A D C`] by blast
		have "A \<noteq> D" using betweennotequal[OF `bet B A D`] by blast
		have "D \<noteq> A" using inequalitysymmetric[OF `A \<noteq> D`] .
		have "col A B C" using collinear4[OF `col D A B` `col D A C` `D \<noteq> A`] .
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A D C" by blast
	have "\<not> (D = C)"
	proof (rule ccontr)
		assume "\<not> (D \<noteq> C)"
		hence "D = C" by blast
		have "col A D C" using collinear_b `D = C` by blast
		show "False" using `col A D C` `\<not> col A D C` by blast
	qed
	hence "D \<noteq> C" by blast
	have "triangle A D C" using triangle_b[OF `\<not> col A D C`] .
	have "tri_isos A D C" using isosceles_b[OF `triangle A D C` `seg_eq A D A C`] .
	have "ang_eq A D C A C D" using Prop05[OF `tri_isos A D C`] .
	have "\<not> (col A C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A C D))"
hence "col A C D" by blast
		have "col A D C" using collinearorder[OF `col A C D`] by blast
		show "False" using `col A D C` `\<not> col A D C` by blast
	qed
	hence "\<not> col A C D" by blast
	have "ang_eq A C D D C A" using ABCequalsCBA[OF `\<not> col A C D`] .
	have "ang_eq A D C D C A" using equalanglestransitive[OF `ang_eq A D C A C D` `ang_eq A C D D C A`] .
	have "D = D" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "\<not> (C = D)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> D)"
		hence "C = D" by blast
		have "col A C D" using collinear_b `C = D` by blast
		show "False" using `col A C D` `\<not> col A C D` by blast
	qed
	hence "C \<noteq> D" by blast
	have "ray_on C D D" using ray4 `D = D` `C \<noteq> D` by blast
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "bet D A B" using betweennesssymmetryE[OF `bet B A D`] .
	have "ang_lt A D C D C B" using anglelessthan_b[OF `bet D A B` `ray_on C D D` `ray_on C B B` `ang_eq A D C D C A`] .
	have "ray_on D A B" using ray4 `bet D A B` `D \<noteq> A` by blast
	have "ray_on D C C" using ray4 `C = C` `D \<noteq> C` by blast
	have "ray_on D B B" using ray4 `B = B` `D \<noteq> B` by blast
	have "seg_eq D B D B" using congruencereflexiveE.
	have "seg_eq D C D C" using congruencereflexiveE.
	have "seg_eq B C B C" using congruencereflexiveE.
	have "\<not> col A D C" using `\<not> col A D C` .
	have "ang_eq A D C B D C" using equalangles_b[OF `ray_on D A B` `ray_on D C C` `ray_on D B B` `ray_on D C C` `seg_eq D B D B` `seg_eq D C D C` `seg_eq B C B C` `\<not> col A D C`] .
	have "ang_eq B D C A D C" using equalanglessymmetric[OF `ang_eq A D C B D C`] .
	have "ang_lt B D C D C B" using angleorderrespectscongruence2[OF `ang_lt A D C D C B` `ang_eq B D C A D C`] .
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C D))"
hence "col B C D" by blast
		have "col B A D" using collinear_b `bet B A D \<and> seg_eq A D C A` by blast
		have "col D B A" using collinearorder[OF `col B A D`] by blast
		have "col D B C" using collinearorder[OF `col B C D`] by blast
		have "B \<noteq> D" using betweennotequal[OF `bet B A D`] by blast
		have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
		have "col B A C" using collinear4[OF `col D B A` `col D B C` `D \<noteq> B`] .
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C D" by blast
	have "\<not> (col C D B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C D B))"
hence "col C D B" by blast
		have "col B C D" using collinearorder[OF `col C D B`] by blast
		show "False" using `col B C D` `\<not> col B C D` by blast
	qed
	hence "\<not> col C D B" by blast
	have "ang_eq C D B B D C" using ABCequalsCBA[OF `\<not> col C D B`] .
	have "ang_eq B C D D C B" using ABCequalsCBA[OF `\<not> col B C D`] .
	have "ang_lt C D B D C B" using angleorderrespectscongruence2[OF `ang_lt B D C D C B` `ang_eq C D B B D C`] .
	have "ang_lt C D B B C D" using angleorderrespectscongruence[OF `ang_lt C D B D C B` `ang_eq B C D D C B`] .
	have "triangle B C D" using triangle_b[OF `\<not> col B C D`] .
	have "ang_lt C D B B C D" using `ang_lt C D B B C D` .
	have "seg_lt B C B D" using Prop19[OF `triangle B C D` `ang_lt C D B B C D`] .
	have "bet B A D" using `bet B A D` .
	have "seg_lt B C B D" using `seg_lt B C B D` .
	have "seg_eq A D A C" using `seg_eq A D A C` .
	have "seg_sum_gt B A A C B C" using togethergreater_b[OF `bet B A D` `seg_eq A D A C` `seg_lt B C B D`] .
	thus ?thesis by blast
qed

end