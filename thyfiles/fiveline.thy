theory fiveline
	imports Axioms Definitions Theorems
begin

theorem fiveline:
	assumes: `axioms`
		"col A B C"
		"seg_eq A B a b"
		"seg_eq B C b c"
		"seg_eq A D a d"
		"seg_eq C D c d"
		"seg_eq A C a c"
		"A \<noteq> C"
	shows: "seg_eq B D b d"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using col_f[OF `axioms` `col A B C`] .
	have "A = B \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B` `A \<noteq> C` by blast
	consider "A = B"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence seg_eq B D b d
	proof (cases)
		case 1
		have "seg_eq B B a b" sorry
		have "seg_eq a b B B" using congruencesymmetric[OF `axioms` `seg_eq B B a b`] .
		have "a = b" using nullsegment1E[OF `axioms` `seg_eq a b B B`] .
		have "seg_eq B D a d" sorry
		have "seg_eq B D b d" sorry
	next
		case 2
		have "seg_eq B B b c" sorry
		have "seg_eq b c B B" using congruencesymmetric[OF `axioms` `seg_eq B B b c`] .
		have "b = c" using nullsegment1E[OF `axioms` `seg_eq b c B B`] .
		have "seg_eq B D c d" sorry
		have "seg_eq B D b d" sorry
	next
		case 3
		have "bet C A B" using betweennesssymmetryE[OF `axioms` `bet B A C`] .
		have "seg_eq C A c a" using congruenceflip[OF `axioms` `seg_eq A C a c`] by blast
		have "seg_eq C B c b" using congruenceflip[OF `axioms` `seg_eq B C b c`] by blast
		have "bet c a b" using betweennesspreserved[OF `axioms` `seg_eq C A c a` `seg_eq C B c b` `seg_eq A B a b` `bet C A B`] .
		have "seg_eq D B d b" using 5-lineE[OF `axioms` `seg_eq A B a b` `seg_eq C D c d` `seg_eq A D a d` `bet C A B` `bet c a b` `seg_eq C A c a`] .
		have "seg_eq B D b d" using congruenceflip[OF `axioms` `seg_eq D B d b`] by blast
	next
		case 4
		have "bet a b c" using betweennesspreserved[OF `axioms` `seg_eq A B a b` `seg_eq A C a c` `seg_eq B C b c` `bet A B C`] .
		have "seg_eq B D b d" using interior5[OF `axioms` `bet A B C` `bet a b c` `seg_eq A B a b` `seg_eq B C b c` `seg_eq A D a d` `seg_eq C D c d`] .
	next
		case 5
		have "seg_eq C B c b" using congruenceflip[OF `axioms` `seg_eq B C b c`] by blast
		have "bet a c b" using betweennesspreserved[OF `axioms` `seg_eq A C a c` `seg_eq A B a b` `seg_eq C B c b` `bet A C B`] .
		have "seg_eq D B d b" using 5-lineE[OF `axioms` `seg_eq C B c b` `seg_eq A D a d` `seg_eq C D c d` `bet A C B` `bet a c b` `seg_eq A C a c`] .
		have "seg_eq B D b d" using congruenceflip[OF `axioms` `seg_eq D B d b`] by blast
	next
	thus ?thesis by blast
qed

end