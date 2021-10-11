theory fiveline
	imports Geometry betweennesspreserved congruenceflip congruencesymmetric interior5
begin

theorem(in euclidean_geometry) fiveline:
	assumes 
		"col A B C"
		"seg_eq A B a b"
		"seg_eq B C b c"
		"seg_eq A D a d"
		"seg_eq C D c d"
		"seg_eq A C a c"
		"A \<noteq> C"
	shows "seg_eq B D b d"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `col A B C`] .
	have "A = B \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B` `A \<noteq> C` by blast
	consider "A = B"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence "seg_eq B D b d"
	proof (cases)
		assume "A = B"
		have "seg_eq B B a b" using `seg_eq A B a b` `A = B` by blast
		have "seg_eq a b B B" using congruencesymmetric[OF `seg_eq B B a b`] .
		have "a = b" using nullsegment1E[OF `seg_eq a b B B`] .
		have "seg_eq B D a d" using `seg_eq A D a d` `A = B` by blast
		have "seg_eq B D b d" using `seg_eq A D a d` `A = B` `a = b` by blast
		thus ?thesis by blast
	next
		assume "B = C"
		have "seg_eq B B b c" using `seg_eq B C b c` `B = C` by blast
		have "seg_eq b c B B" using congruencesymmetric[OF `seg_eq B B b c`] .
		have "b = c" using nullsegment1E[OF `seg_eq b c B B`] .
		have "seg_eq B D c d" using `seg_eq C D c d` `B = C` by blast
		have "seg_eq B D b d" using `seg_eq B D c d` `b = c` by blast
		thus ?thesis by blast
	next
		assume "bet B A C"
		have "bet C A B" using betweennesssymmetryE[OF `bet B A C`] .
		have "seg_eq C A c a" using congruenceflip[OF `seg_eq A C a c`] by blast
		have "seg_eq C B c b" using congruenceflip[OF `seg_eq B C b c`] by blast
		have "bet c a b" using betweennesspreserved[OF `seg_eq C A c a` `seg_eq C B c b` `seg_eq A B a b` `bet C A B`] .
		have "seg_eq D B d b" using n5_lineE[OF `seg_eq A B a b` `seg_eq C D c d` `seg_eq A D a d` `bet C A B` `bet c a b` `seg_eq C A c a`] .
		have "seg_eq B D b d" using congruenceflip[OF `seg_eq D B d b`] by blast
		thus ?thesis by blast
	next
		assume "bet A B C"
		have "bet a b c" using betweennesspreserved[OF `seg_eq A B a b` `seg_eq A C a c` `seg_eq B C b c` `bet A B C`] .
		have "seg_eq B D b d" using interior5[OF `bet A B C` `bet a b c` `seg_eq A B a b` `seg_eq B C b c` `seg_eq A D a d` `seg_eq C D c d`] .
		thus ?thesis by blast
	next
		assume "bet A C B"
		have "seg_eq C B c b" using congruenceflip[OF `seg_eq B C b c`] by blast
		have "bet a c b" using betweennesspreserved[OF `seg_eq A C a c` `seg_eq A B a b` `seg_eq C B c b` `bet A C B`] .
		have "seg_eq D B d b" using n5_lineE[OF `seg_eq C B c b` `seg_eq A D a d` `seg_eq C D c d` `bet A C B` `bet a c b` `seg_eq A C a c`] .
		have "seg_eq B D b d" using congruenceflip[OF `seg_eq D B d b`] by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end