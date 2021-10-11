theory collinearright
	imports n8_2 n8_3 Geometry betweennotequal collinearorder congruencesymmetric equalitysymmetric inequalitysymmetric ray4 ray5 rightangleNC
begin

theorem(in euclidean_geometry) collinearright:
	assumes 
		"ang_right A B D"
		"col A B C"
		"C \<noteq> B"
	shows "ang_right C B D"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `col A B C`] .
	have "\<not> col A B D" using rightangleNC[OF `ang_right A B D`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "\<not> col A A D" using `\<not> col A B D` `A = B` by blast
		have "A = A" using equalityreflexiveE.
		have "col D A A" using collinear_b `A = A` by blast
		have "col A A D" using collinearorder[OF `col D A A`] by blast
		show "False" using `col A A D` `\<not> col A A D` by blast
	qed
	hence "A \<noteq> B" by blast
	have "ang_right D B A" using n8_2[OF `ang_right A B D`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence "ang_right D B C"
	proof (cases)
		assume "A = B"
		have "\<not> (\<not> (ang_right D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ang_right D B C)))"
hence "\<not> (ang_right D B C)" by blast
			have "col A B D" using collinear_b `A = B` by blast
			show "False" using `col A B D` `\<not> col A B D` by blast
		qed
		hence "ang_right D B C" by blast
		thus ?thesis by blast
	next
		assume "A = C"
		have "ang_right D B C" using `ang_right D B A` `A = C` by blast
		thus ?thesis by blast
	next
		assume "B = C"
		have "\<not> (\<not> (ang_right D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ang_right D B C)))"
hence "\<not> (ang_right D B C)" by blast
			have "C = B" using equalitysymmetric[OF `B = C`] .
			have "C \<noteq> B" using `C \<noteq> B` .
			show "False" using `C \<noteq> B` `C = B` by blast
		qed
		hence "ang_right D B C" by blast
		thus ?thesis by blast
	next
		assume "bet B A C"
		have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
		have "ray_on B A C" using ray4 `bet B A C` `B \<noteq> A` by blast
		have "ang_right D B C" using n8_3[OF `ang_right D B A` `ray_on B A C`] .
		thus ?thesis by blast
	next
		assume "bet A B C"
		obtain E where "bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D" using rightangle_f[OF `ang_right A B D`]  by  blast
		have "seg_eq A B E B" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "seg_eq A D E D" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "bet A B E" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "B \<noteq> D" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "bet E B A" using betweennesssymmetryE[OF `bet A B E`] .
		have "seg_eq E B A B" using congruencesymmetric[OF `seg_eq A B E B`] .
		have "seg_eq E D A D" using congruencesymmetric[OF `seg_eq A D E D`] .
		have "bet E B A \<and> seg_eq E B A B \<and> seg_eq A D E D \<and> B \<noteq> D" using `bet E B A` `seg_eq E B A B` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "ang_right E B D" using rightangle_b[OF `bet E B A` `seg_eq E B A B` `seg_eq E D A D` `B \<noteq> D`] .
		have "ang_right D B E" using n8_2[OF `ang_right E B D`] .
		have "bet A B E" using betweennesssymmetryE[OF `bet E B A`] .
		have "bet A B C \<and> bet A B E" using `bet A B C` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "ray_on B E C" using ray_b[OF `bet A B C` `bet A B E`] .
		have "ang_right D B C" using n8_3[OF `ang_right D B E` `ray_on B E C`] .
		thus ?thesis by blast
	next
		assume "bet A C B"
		have "bet B C A" using betweennesssymmetryE[OF `bet A C B`] .
		have "C \<noteq> B" using betweennotequal[OF `bet A C B`] by blast
		have "B \<noteq> C" using inequalitysymmetric[OF `C \<noteq> B`] .
		have "ray_on B C A" using ray4 `bet B C A` `B \<noteq> C` by blast
		have "ang_right D B A" using n8_2[OF `ang_right A B D`] .
		have "ray_on B A C" using ray5[OF `ray_on B C A`] .
		have "ang_right D B C" using n8_3[OF `ang_right D B A` `ray_on B A C`] .
		thus ?thesis by blast
	qed
	have "ang_right C B D" using n8_2[OF `ang_right D B C`] .
	thus ?thesis by blast
qed

end