theory together
	imports Geometry betweennotequal congruencesymmetric congruencetransitive lessthancongruence lessthancongruence2 nullsegment3 sumofparts
begin

theorem(in euclidean_geometry) together:
	assumes 
		"seg_sum_gt A a B b C c"
		"seg_eq D F A a"
		"seg_eq F G B b"
		"bet D F G"
		"seg_eq P Q C c"
	shows "seg_lt P Q D G \<and> A \<noteq> a \<and> B \<noteq> b \<and> C \<noteq> c"
proof -
	obtain R where "bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R" using togethergreater_f[OF `seg_sum_gt A a B b C c`]  by  blast
	have "bet A a R" using `bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R` by blast
	have "seg_eq a R B b" using `bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R` by blast
	have "seg_lt C c A R" using `bet A a R \<and> seg_eq a R B b \<and> seg_lt C c A R` by blast
	have "seg_eq B b a R" using congruencesymmetric[OF `seg_eq a R B b`] .
	have "seg_eq F G a R" using congruencetransitive[OF `seg_eq F G B b` `seg_eq B b a R`] .
	have "seg_eq D G A R" using sumofparts[OF `seg_eq D F A a` `seg_eq F G a R` `bet D F G` `bet A a R`] .
	have "seg_eq A R D G" using congruencesymmetric[OF `seg_eq D G A R`] .
	have "seg_eq C c P Q" using congruencesymmetric[OF `seg_eq P Q C c`] .
	have "seg_lt P Q A R" using lessthancongruence2[OF `seg_lt C c A R` `seg_eq C c P Q`] .
	have "seg_lt P Q D G" using lessthancongruence[OF `seg_lt P Q A R` `seg_eq A R D G`] .
	have "A \<noteq> a" using betweennotequal[OF `bet A a R`] by blast
	have "a \<noteq> R" using betweennotequal[OF `bet A a R`] by blast
	have "B \<noteq> b" using nullsegment3[OF `a \<noteq> R` `seg_eq a R B b`] .
	obtain S where "bet A S R \<and> seg_eq A S C c" using lessthan_f[OF `seg_lt C c A R`]  by  blast
	have "bet A S R" using `bet A S R \<and> seg_eq A S C c` by blast
	have "seg_eq A S C c" using `bet A S R \<and> seg_eq A S C c` by blast
	have "A \<noteq> S" using betweennotequal[OF `bet A S R`] by blast
	have "C \<noteq> c" using nullsegment3[OF `A \<noteq> S` `seg_eq A S C c`] .
	have "seg_lt P Q D G \<and> A \<noteq> a \<and> B \<noteq> b \<and> C \<noteq> c" using `seg_lt P Q D G` `A \<noteq> a` `B \<noteq> b` `C \<noteq> c` by blast
	thus ?thesis by blast
qed

end