theory rightangleNC
	imports Geometry betweennotequal collinear4 collinearorder congruenceflip congruencesymmetric doublereverse equalitysymmetric inequalitysymmetric midpointunique partnotequalwhole
begin

theorem(in euclidean_geometry) rightangleNC:
	assumes 
		"ang_right A B C"
	shows "\<not> col A B C"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" using rightangle_f[OF `ang_right A B C`]  by  blast
	have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B B D" using congruenceflip[OF `seg_eq A B D B`] by blast
	have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "midpoint A B D" using midpoint_b[OF `bet A B D` `seg_eq A B B D`] .
	have "\<not> (bet A C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet A C D))"
hence "bet A C D" by blast
		have "seg_eq A C C D" using congruenceflip[OF `seg_eq A C D C`] by blast
		have "midpoint A C D" using midpoint_b[OF `bet A C D` `seg_eq A C C D`] .
		have "B = C" using midpointunique[OF `midpoint A B D` `midpoint A C D`] .
		show "False" using `B = C` `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	qed
	hence "\<not> (bet A C D)" by blast
	have "A \<noteq> B" using betweennotequal[OF `bet A B D`] by blast
	have "\<not> (C = A)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> A)"
		hence "C = A" by blast
		have "seg_eq A C D C" using `seg_eq A C D C` .
		have "seg_eq C C D C" using `seg_eq A C D C` `C = A` by blast
		have "seg_eq D C C C" using congruencesymmetric[OF `seg_eq C C D C`] .
		have "D = C" using nullsegment1E[OF `seg_eq D C C C`] .
		have "A = C" using equalitysymmetric[OF `C = A`] .
		have "D = A" using equalitytransitiveE[OF `D = C` `A = C`] .
		have "A = D" using equalitysymmetric[OF `D = A`] .
		have "A \<noteq> D" using betweennotequal[OF `bet A B D`] by blast
		show "False" using `A \<noteq> D` `A = D` by blast
	qed
	hence "C \<noteq> A" by blast
	have "\<not> (C = D)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> D)"
		hence "C = D" by blast
		have "seg_eq A C D C" using `seg_eq A C D C` .
		have "seg_eq A C D D" using `seg_eq A C D C` `C = D` by blast
		have "A = C" using nullsegment1E[OF `seg_eq A C D D`] .
		have "C = A" using equalitysymmetric[OF `A = C`] .
		show "False" using `C = A` `C \<noteq> A` by blast
	qed
	hence "C \<noteq> D" by blast
	have "\<not> (bet C A D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet C A D))"
hence "bet C A D" by blast
		have "seg_eq C A C D" using congruenceflip[OF `seg_eq A C D C`] by blast
		have "\<not> (seg_eq C A C D)" using partnotequalwhole[OF `bet C A D`] .
		show "False" using `\<not> (seg_eq C A C D)` `seg_eq C A C D` by blast
	qed
	hence "\<not> (bet C A D)" by blast
	have "\<not> (bet A D C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet A D C))"
hence "bet A D C" by blast
		have "bet C D A" using betweennesssymmetryE[OF `bet A D C`] .
		have "seg_eq C D C A" using doublereverse[OF `seg_eq A C D C`] by blast
		have "\<not> (seg_eq C D C A)" using partnotequalwhole[OF `bet C D A`] .
		show "False" using `\<not> (seg_eq C D C A)` `seg_eq C D C A` by blast
	qed
	hence "\<not> (bet A D C)" by blast
	have "\<not> (col A B C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
		have "col A B D" using collinear_b `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "col B A C" using collinearorder[OF `col A B C`] by blast
		have "col B A D" using collinearorder[OF `col A B D`] by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
		have "col A C D" using collinear4[OF `col B A C` `col B A D` `B \<noteq> A`] .
		have "A = C \<or> A = D \<or> C = D \<or> bet C A D \<or> bet A C D \<or> bet A D C" using collinear_f[OF `col A C D`] .
		consider "A = C"|"A = D"|"C = D"|"bet C A D"|"bet A C D"|"bet A D C" using `A = C \<or> A = D \<or> C = D \<or> bet C A D \<or> bet A C D \<or> bet A D C`  by blast
		hence "\<not> col A B C"
		proof (cases)
			assume "A = C"
			have "\<not> (col A B C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
				have "A \<noteq> C" using inequalitysymmetric[OF `C \<noteq> A`] .
				show "False" using `A \<noteq> C` `A = C` by blast
			qed
			hence "\<not> col A B C" by blast
			thus ?thesis by blast
		next
			assume "A = D"
			have "\<not> (col A B C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
				have "A \<noteq> D" using betweennotequal[OF `bet A B D`] by blast
				show "False" using `A \<noteq> D` `A = D` by blast
			qed
			hence "\<not> col A B C" by blast
			thus ?thesis by blast
		next
			assume "C = D"
			have "\<not> (col A B C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
				have "C \<noteq> D" using `C \<noteq> D` .
				show "False" using `C \<noteq> D` `C = D` by blast
			qed
			hence "\<not> col A B C" by blast
			thus ?thesis by blast
		next
			assume "bet C A D"
			have "\<not> (col A B C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
				have "\<not> (bet C A D)" using `\<not> (bet C A D)` .
				show "False" using `\<not> (bet C A D)` `bet C A D` by blast
			qed
			hence "\<not> col A B C" by blast
			thus ?thesis by blast
		next
			assume "bet A C D"
			have "\<not> (col A B C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
				have "\<not> (bet A C D)" using `\<not> (bet A C D)` .
				show "False" using `\<not> (bet A C D)` `bet A C D` by blast
			qed
			hence "\<not> col A B C" by blast
			thus ?thesis by blast
		next
			assume "bet A D C"
			have "\<not> (col A B C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
				have "\<not> (bet A D C)" using `\<not> (bet A D C)` .
				show "False" using `\<not> (bet A D C)` `bet A D C` by blast
			qed
			hence "\<not> col A B C" by blast
			thus ?thesis by blast
		qed
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col A B C" by blast
	thus ?thesis by blast
qed

end