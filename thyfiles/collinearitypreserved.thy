theory collinearitypreserved
	imports Axioms Definitions Theorems
begin

theorem collinearitypreserved:
	assumes: `axioms`
		"col A B C"
		"seg_eq A B a b"
		"seg_eq A C a c"
		"seg_eq B C b c"
	shows: "col a b c"
proof -
	have "seg_eq C B B C" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq C B b c" using congruencetransitive[OF `axioms` `seg_eq C B B C` `seg_eq B C b c`] .
	have "seg_eq b c c b" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq C B c b" using congruencetransitive[OF `axioms` `seg_eq C B b c` `seg_eq b c c b`] .
	have "seg_eq a b b a" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq A B b a" using congruencetransitive[OF `axioms` `seg_eq A B a b` `seg_eq a b b a`] .
	have "seg_eq A B B A" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq B A A B" using congruencesymmetric[OF `axioms` `seg_eq A B B A`] .
	have "seg_eq B A b a" using congruencetransitive[OF `axioms` `seg_eq B A A B` `seg_eq A B b a`] .
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence col a b c
	proof (cases)
		case 1
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A A a b" using `seg_eq A B a b` `A = B` by blast
		have "seg_eq a b A A" using congruencesymmetric[OF `axioms` `seg_eq A A a b`] .
		have "a = b" using nullsegment1E[OF `axioms` `seg_eq a b A A`] .
		have "col a b c" using collinear_b `axioms` `a = b` by blast
	next
		case 2
		have "seg_eq A C a c" using `seg_eq A C a c` .
		have "seg_eq A A a c" using `seg_eq A C a c` `A = C` by blast
		have "seg_eq a c A A" using congruencesymmetric[OF `axioms` `seg_eq A A a c`] .
		have "a = c" using nullsegment1E[OF `axioms` `seg_eq a c A A`] .
		have "col a b c" using collinear_b `axioms` `a = c` by blast
	next
		case 3
		have "seg_eq B C b c" using `seg_eq B C b c` .
		have "seg_eq B B b c" using `seg_eq B C b c` `B = C` by blast
		have "seg_eq b c B B" using congruencesymmetric[OF `axioms` `seg_eq B B b c`] .
		have "b = c" using nullsegment1E[OF `axioms` `seg_eq b c B B`] .
		have "col a b c" using collinear_b `axioms` `b = c` by blast
	next
		case 4
		have "bet b a c" using betweennesspreserved[OF `axioms` `seg_eq B A b a` `seg_eq B C b c` `seg_eq A C a c` `bet B A C`] .
		have "col a b c" using collinear_b `axioms` `bet b a c` by blast
	next
		case 5
		have "bet a b c" using betweennesspreserved[OF `axioms` `seg_eq A B a b` `seg_eq A C a c` `seg_eq B C b c` `bet A B C`] .
		have "col a b c" using collinear_b `axioms` `bet a b c` by blast
	next
		case 6
		have "bet a c b" using betweennesspreserved[OF `axioms` `seg_eq A C a c` `seg_eq A B a b` `seg_eq C B c b` `bet A C B`] .
		have "col a b c" using collinear_b `axioms` `bet a c b` by blast
	next
	thus ?thesis by blast
qed

end