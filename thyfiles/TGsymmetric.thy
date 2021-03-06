theory TGsymmetric
	imports Geometry betweennotequal congruenceflip doublereverse lessthancongruence nullsegment3 sumofparts
begin

theorem(in euclidean_geometry) TGsymmetric:
	assumes 
		"seg_sum_gt A a B b C c"
	shows "seg_sum_gt B b A a C c"
proof -
	obtain H where "bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H" using togethergreater_f[OF `seg_sum_gt A a B b C c`]  by  blast
	have "bet A a H" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "seg_eq a H B b" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "seg_lt C c A H" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "a \<noteq> H" using betweennotequal[OF `bet A a H`] by blast
	have "B \<noteq> b" using nullsegment3[OF `a \<noteq> H` `seg_eq a H B b`] .
	have "A \<noteq> a" using betweennotequal[OF `bet A a H`] by blast
	obtain F where "bet B b F \<and> seg_eq b F A a" using extensionE[OF `B \<noteq> b` `A \<noteq> a`]  by  blast
	have "bet B b F" using `bet B b F \<and> seg_eq b F A a` by blast
	have "seg_eq b F A a" using `bet B b F \<and> seg_eq b F A a` by blast
	have "seg_eq a A F b" using doublereverse[OF `seg_eq b F A a`] by blast
	have "seg_eq A a F b" using congruenceflip[OF `seg_eq a A F b`] by blast
	have "seg_eq a H b B" using congruenceflip[OF `seg_eq a H B b`] by blast
	have "bet F b B" using betweennesssymmetryE[OF `bet B b F`] .
	have "seg_eq A H F B" using sumofparts[OF `seg_eq A a F b` `seg_eq a H b B` `bet A a H` `bet F b B`] .
	have "seg_eq A H B F" using congruenceflip[OF `seg_eq A H F B`] by blast
	have "seg_lt C c B F" using lessthancongruence[OF `seg_lt C c A H` `seg_eq A H B F`] .
	have "seg_sum_gt B b A a C c" using togethergreater_b[OF `bet B b F` `seg_eq b F A a` `seg_lt C c B F`] .
	thus ?thesis by blast
qed

end