theory betweennesspreserved
	imports Axioms Definitions Theorems
begin

theorem betweennesspreserved:
	assumes: `axioms`
		"seg_eq A B a b"
		"seg_eq A C a c"
		"seg_eq B C b c"
		"bet A B C"
	shows: "bet a b c"
proof -
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B C`] by blast
	have "seg_eq A B a b" using `seg_eq A B a b` .
	have "a \<noteq> b" using nullsegment3[OF `axioms` `A \<noteq> B` `seg_eq A B a b`] .
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet A B C`] by blast
	obtain d where "bet a b d \<and> seg_eq b d B C" using extensionE[OF `axioms` `a \<noteq> b` `B \<noteq> C`] by blast
	have "bet a b d" using `bet a b d \<and> seg_eq b d B C` by blast
	have "seg_eq b d B C" using `bet a b d \<and> seg_eq b d B C` by blast
	have "seg_eq A B a b" using `seg_eq A B a b` .
	have "seg_eq B C b d" using congruencesymmetric[OF `axioms` `seg_eq b d B C`] .
	have "seg_eq B C b c" using `seg_eq B C b c` .
	have "seg_eq A C a c" using `seg_eq A C a c` .
	have "seg_eq C C c d" using 5-lineE[OF `axioms` `seg_eq B C b d` `seg_eq A C a c` `seg_eq B C b c` `bet A B C` `bet a b d` `seg_eq A B a b`] .
	have "seg_eq c d C C" using congruencesymmetric[OF `axioms` `seg_eq C C c d`] .
	have "c = d" using nullsegment1E[OF `axioms` `seg_eq c d C C`] .
	have "bet a b c" using `bet a b d` `c = d` by blast
	thus ?thesis by blast
qed

end