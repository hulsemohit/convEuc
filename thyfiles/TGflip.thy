theory TGflip
	imports Geometry betweennotequal congruencesymmetric congruencetransitive inequalitysymmetric lessthancongruence lessthancongruence2 nullsegment3 sumofparts
begin

theorem(in euclidean_geometry) TGflip:
	assumes 
		"seg_sum_gt A a B b C c"
	shows "seg_sum_gt a A B b C c \<and> seg_sum_gt A a B b c C"
proof -
	obtain H where "bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H" using togethergreater_f[OF `seg_sum_gt A a B b C c`]  by  blast
	have "bet A a H" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "seg_eq a H B b" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "seg_lt C c A H" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "A \<noteq> a" using betweennotequal[OF `bet A a H`] by blast
	have "a \<noteq> A" using inequalitysymmetric[OF `A \<noteq> a`] .
	have "a \<noteq> H" using betweennotequal[OF `bet A a H`] by blast
	have "B \<noteq> b" using nullsegment3[OF `a \<noteq> H` `seg_eq a H B b`] .
	obtain h where "bet a A h \<and> seg_eq A h B b" using extensionE[OF `a \<noteq> A` `B \<noteq> b`]  by  blast
	have "seg_eq A a a A" using equalityreverseE.
	have "seg_eq a H B b" using `seg_eq a H B b` .
	have "seg_eq A h B b" using `bet a A h \<and> seg_eq A h B b` by blast
	have "seg_eq B b A h" using congruencesymmetric[OF `seg_eq A h B b`] .
	have "seg_eq a H A h" using congruencetransitive[OF `seg_eq a H B b` `seg_eq B b A h`] .
	have "bet A a H" using `bet A a H` .
	have "bet a A h" using `bet a A h \<and> seg_eq A h B b` by blast
	have "seg_eq A H a h" using sumofparts[OF `seg_eq A a a A` `seg_eq a H A h` `bet A a H` `bet a A h`] .
	have "seg_lt C c a h" using lessthancongruence[OF `seg_lt C c A H` `seg_eq A H a h`] .
	have "seg_sum_gt a A B b C c" using togethergreater_b[OF `bet a A h` `seg_eq A h B b` `seg_lt C c a h`] .
	have "seg_eq C c c C" using equalityreverseE.
	have "seg_lt c C A H" using lessthancongruence2[OF `seg_lt C c A H` `seg_eq C c c C`] .
	have "seg_sum_gt A a B b c C" using togethergreater_b[OF `bet A a H` `seg_eq a H B b` `seg_lt c C A H`] .
	have "seg_sum_gt a A B b C c \<and> seg_sum_gt A a B b c C" using `seg_sum_gt a A B b C c` `seg_sum_gt A a B b c C` by blast
	thus ?thesis by blast
qed

end