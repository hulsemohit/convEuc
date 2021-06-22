theory together
	imports Axioms Definitions Theorems
begin

theorem together:
	assumes: `axioms`
		"seg_sum_gt A a B b C c"
		"seg_eq D F A a"
		"seg_eq F G B b"
		"bet D F G"
		"seg_eq P Q C c"
	shows: "seg_lt P Q D G \<and> A \<noteq> a \<and> B \<noteq> b \<and> C \<noteq> c"
proof -
	obtain R where "bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R" sorry
	have "bet A a R" using `bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R` by blast
	have "seg_eq a R B b" using `bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R` by blast
	have "seg_lt C c A R" using `bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R` by blast
	have "seg_eq B b a R" using congruencesymmetric[OF `axioms` `seg_eq a R B b`] .
	have "seg_eq F G a R" using congruencetransitive[OF `axioms` `seg_eq F G B b` `seg_eq B b a R`] .
	have "seg_eq D G A R" using sumofparts[OF `axioms` `seg_eq D F A a` `seg_eq F G a R` `bet D F G` `bet A a R`] .
	have "seg_eq A R D G" using congruencesymmetric[OF `axioms` `seg_eq D G A R`] .
	have "seg_eq C c P Q" using congruencesymmetric[OF `axioms` `seg_eq P Q C c`] .
	have "seg_lt P Q A R" using lessthancongruence2[OF `axioms` `seg_lt C c A R` `seg_eq C c P Q`] .
	have "seg_lt P Q D G" using lessthancongruence[OF `axioms` `seg_lt P Q A R` `seg_eq A R D G`] .
	have "A \<noteq> a" using betweennotequal[OF `axioms` `bet A a R`] by blast
	have "a \<noteq> R" using betweennotequal[OF `axioms` `bet A a R`] by blast
	have "B \<noteq> b" using nullsegment3[OF `axioms` `a \<noteq> R` `seg_eq a R B b`] .
	obtain S where "bet A S R \<and> seg_eq A S C c" sorry
	have "bet A S R" using `bet A S R \<and> seg_eq A S C c` by blast
	have "seg_eq A S C c" using `bet A S R \<and> seg_eq A S C c` by blast
	have "A \<noteq> S" using betweennotequal[OF `axioms` `bet A S R`] by blast
	have "C \<noteq> c" using nullsegment3[OF `axioms` `A \<noteq> S` `seg_eq A S C c`] .
	have "seg_lt P Q D G \<and> A \<noteq> a \<and> B \<noteq> b \<and> C \<noteq> c" using `seg_lt P Q D G` `A \<noteq> a` `B \<noteq> b` `C \<noteq> c` by blast
	thus ?thesis by blast
qed

end