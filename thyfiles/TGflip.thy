theory TGflip
	imports Axioms Definitions Theorems
begin

theorem TGflip:
	assumes: `axioms`
		"seg_sum_gt A a B b C c"
	shows: "seg_sum_gt a A B b C c \<and> seg_sum_gt A a B b c C"
proof -
	obtain H where "bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H" sorry
	have "bet A a H" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "seg_eq a H B b" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "seg_lt C c A H" using `bet A a H \<and> seg_eq a H B b \<and> seg_lt C c A H` by blast
	have "A \<noteq> a" using betweennotequal[OF `axioms` `bet A a H`] by blast
	have "a \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> a`] .
	have "a \<noteq> H" using betweennotequal[OF `axioms` `bet A a H`] by blast
	have "B \<noteq> b" using nullsegment3[OF `axioms` `a \<noteq> H` `seg_eq a H B b`] .
	obtain h where "bet a A h \<and> seg_eq A h B b" using extensionE[OF `axioms` `a \<noteq> A` `B \<noteq> b`]  by  blast
	have "seg_eq A a a A" using equalityreverseE[OF `axioms`] .
	have "seg_eq a H B b" using `seg_eq a H B b` .
	have "seg_eq A h B b" using `bet a A h \<and> seg_eq A h B b` by blast
	have "seg_eq B b A h" using congruencesymmetric[OF `axioms` `seg_eq A h B b`] .
	have "seg_eq a H A h" using congruencetransitive[OF `axioms` `seg_eq a H B b` `seg_eq B b A h`] .
	have "bet A a H" using `bet A a H` .
	have "bet a A h" using `bet a A h \<and> seg_eq A h B b` by blast
	have "seg_eq A H a h" using sumofparts[OF `axioms` `seg_eq A a a A` `seg_eq a H A h` `bet A a H` `bet a A h`] .
	have "seg_lt C c a h" using lessthancongruence[OF `axioms` `seg_lt C c A H` `seg_eq A H a h`] .
	have "seg_sum_gt a A B b C c" sorry
	have "seg_eq C c c C" using equalityreverseE[OF `axioms`] .
	have "seg_lt c C A H" using lessthancongruence2[OF `axioms` `seg_lt C c A H` `seg_eq C c c C`] .
	have "seg_sum_gt A a B b c C" sorry
	have "seg_sum_gt a A B b C c \<and> seg_sum_gt A a B b c C" using `seg_sum_gt a A B b C c` `seg_sum_gt A a B b c C` by blast
	thus ?thesis by blast
qed

end