theory Prop20
	imports Axioms Definitions Theorems
begin

theorem Prop20:
	assumes: `axioms`
		"triangle A B C"
	shows: "seg_sum_gt B A A C B C"
proof -
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "B = A"
		have "col B A C" using collinear_b `axioms` `B = A` by blast
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "\<not> (C = A)"
	proof (rule ccontr)
		assume "C = A"
		have "col B C A" using collinear_b `axioms` `C = A` by blast
		have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "C \<noteq> A" by blast
	obtain D where "bet B A D \<and> seg_eq A D C A" using extensionE[OF `axioms` `B \<noteq> A` `C \<noteq> A`] by blast
	have "bet B A D" using `bet B A D \<and> seg_eq A D C A` by blast
	have "A \<noteq> D" using betweennotequal[OF `axioms` `bet B A D`] by blast
	have "D \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> D`] .
	have "B \<noteq> D" using betweennotequal[OF `axioms` `bet B A D`] by blast
	have "D \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> D`] .
	have "seg_eq A D C A" using `bet B A D \<and> seg_eq A D C A` by blast
	have "seg_eq A D A C" using congruenceflip[OF `axioms` `seg_eq A D C A`] by blast
	have "\<not> (col A D C)"
	proof (rule ccontr)
		assume "col A D C"
		have "col B A D" using collinear_b `axioms` `bet B A D \<and> seg_eq A D C A` by blast
		have "col D A B" using collinearorder[OF `axioms` `col B A D`] by blast
		have "col D A C" using collinearorder[OF `axioms` `col A D C`] by blast
		have "A \<noteq> D" using betweennotequal[OF `axioms` `bet B A D`] by blast
		have "D \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> D`] .
		have "col A B C" using collinear4[OF `axioms` `col D A B` `col D A C` `D \<noteq> A`] .
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A D C" by blast
	have "\<not> (D = C)"
	proof (rule ccontr)
		assume "D = C"
		have "col A D C" using collinear_b `axioms` `D = C` by blast
		show "False" using `col A D C` `\<not> col A D C` by blast
	qed
	hence "D \<noteq> C" by blast
	have "triangle A D C" using triangle_b[OF `axioms` `\<not> col A D C`] .
	have "tri_isos A D C" using isosceles_b[OF `axioms` `triangle A D C` `seg_eq A D A C`] .
	have "ang_eq A D C A C D" using Prop05[OF `axioms` `tri_isos A D C`] .
	have "\<not> (col A C D)"
	proof (rule ccontr)
		assume "col A C D"
		have "col A D C" using collinearorder[OF `axioms` `col A C D`] by blast
		show "False" using `col A D C` `\<not> col A D C` by blast
	qed
	hence "\<not> col A C D" by blast
	have "ang_eq A C D D C A" using ABCequalsCBA[OF `axioms` `\<not> col A C D`] .
	have "ang_eq A D C D C A" using equalanglestransitive[OF `axioms` `ang_eq A D C A C D` `ang_eq A C D D C A`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "\<not> (C = D)"
	proof (rule ccontr)
		assume "C = D"
		have "col A C D" using collinear_b `axioms` `C = D` by blast
		show "False" using `col A C D` `\<not> col A C D` by blast
	qed
	hence "C \<noteq> D" by blast
	have "ray_on C D D" using ray4 `axioms` `D = D` `C \<noteq> D` by blast
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "bet D A B" using betweennesssymmetryE[OF `axioms` `bet B A D`] .
	have "ang_lt A D C D C B" using anglelessthan_b[OF `axioms` `bet D A B` `ray_on C D D` `ray_on C B B` `ang_eq A D C D C A`] .
	have "ray_on D A B" using ray4 `axioms` `bet D A B` `D \<noteq> A` by blast
	have "ray_on D C C" using ray4 `axioms` `C = C` `D \<noteq> C` by blast
	have "ray_on D B B" using ray4 `axioms` `B = B` `D \<noteq> B` by blast
	have "seg_eq D B D B" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq D C D C" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] by blast
	have "\<not> col A D C" using `\<not> col A D C` .
	have "ang_eq A D C B D C" using equalangles_b[OF `axioms` `ray_on D A B` `ray_on D C C` `ray_on D B B` `ray_on D C C` `seg_eq D B D B` `seg_eq D C D C` `seg_eq B C B C` `\<not> col A D C`] .
	have "ang_eq B D C A D C" using equalanglessymmetric[OF `axioms` `ang_eq A D C B D C`] .
	have "ang_lt B D C D C B" using angleorderrespectscongruence2[OF `axioms` `ang_lt A D C D C B` `ang_eq B D C A D C`] .
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "col B C D"
		have "col B A D" using collinear_b `axioms` `bet B A D \<and> seg_eq A D C A` by blast
		have "col D B A" using collinearorder[OF `axioms` `col B A D`] by blast
		have "col D B C" using collinearorder[OF `axioms` `col B C D`] by blast
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet B A D`] by blast
		have "D \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> D`] .
		have "col B A C" using collinear4[OF `axioms` `col D B A` `col D B C` `D \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C D" by blast
	have "\<not> (col C D B)"
	proof (rule ccontr)
		assume "col C D B"
		have "col B C D" using collinearorder[OF `axioms` `col C D B`] by blast
		show "False" using `col B C D` `\<not> col B C D` by blast
	qed
	hence "\<not> col C D B" by blast
	have "ang_eq C D B B D C" using ABCequalsCBA[OF `axioms` `\<not> col C D B`] .
	have "ang_eq B C D D C B" using ABCequalsCBA[OF `axioms` `\<not> col B C D`] .
	have "ang_lt C D B D C B" using angleorderrespectscongruence2[OF `axioms` `ang_lt B D C D C B` `ang_eq C D B B D C`] .
	have "ang_lt C D B B C D" using angleorderrespectscongruence[OF `axioms` `ang_lt C D B D C B` `ang_eq B C D D C B`] .
	have "triangle B C D" using triangle_b[OF `axioms` `\<not> col B C D`] .
	have "ang_lt C D B B C D" using `ang_lt C D B B C D` .
	have "seg_lt B C B D" using Prop19[OF `axioms` `triangle B C D` `ang_lt C D B B C D`] .
	have "bet B A D" using `bet B A D` .
	have "seg_lt B C B D" using `seg_lt B C B D` .
	have "seg_eq A D A C" using `seg_eq A D A C` .
	have "seg_sum_gt B A A C B C" using togethergreater_b[OF `axioms` `bet B A D` `seg_eq A D A C` `seg_lt B C B D`] .
	thus ?thesis by blast
qed

end