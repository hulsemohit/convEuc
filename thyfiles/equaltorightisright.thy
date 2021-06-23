theory equaltorightisright
	imports n8_2 n8_3 Geometry congruenceflip congruencesymmetric congruencetransitive doublereverse equalanglessymmetric inequalitysymmetric nullsegment3 ray5 raystrict sumofparts
begin

theorem equaltorightisright:
	assumes "axioms"
		"ang_right A B C"
		"ang_eq a b c A B C"
	shows "ang_right a b c"
proof -
	have "ang_eq A B C a b c" using equalanglessymmetric[OF `axioms` `ang_eq a b c A B C`] .
	obtain E F e f where "ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C" using equalangles_f[OF `axioms` `ang_eq A B C a b c`]  by  blast
	have "ray_on B A E" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "ray_on B C F" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "ray_on b a e" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "ray_on b c f" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "seg_eq B E b e" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "seg_eq B F b f" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "seg_eq E F e f" using `ray_on B A E \<and> ray_on B C F \<and> ray_on b a e \<and> ray_on b c f \<and> seg_eq B E b e \<and> seg_eq B F b f \<and> seg_eq E F e f \<and> \<not> col A B C` by blast
	have "ang_right A B F" using n8_3[OF `axioms` `ang_right A B C` `ray_on B C F`] .
	have "ang_right F B A" using n8_2[OF `axioms` `ang_right A B F`] .
	have "ang_right F B E" using n8_3[OF `axioms` `ang_right F B A` `ray_on B A E`] .
	have "ang_right E B F" using n8_2[OF `axioms` `ang_right F B E`] .
	have "B \<noteq> E" using raystrict[OF `axioms` `ray_on B A E`] .
	have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
	obtain W where "bet E B W \<and> seg_eq E B W B \<and> seg_eq E F W F \<and> B \<noteq> F" using rightangle_f[OF `axioms` `ang_right E B F`]  by  blast
	have "bet E B W" using `bet E B W \<and> seg_eq E B W B \<and> seg_eq E F W F \<and> B \<noteq> F` by blast
	have "seg_eq E B W B" using `bet E B W \<and> seg_eq E B W B \<and> seg_eq E F W F \<and> B \<noteq> F` by blast
	have "seg_eq E F W F" using `bet E B W \<and> seg_eq E B W B \<and> seg_eq E F W F \<and> B \<noteq> F` by blast
	have "B \<noteq> F" using `bet E B W \<and> seg_eq E B W B \<and> seg_eq E F W F \<and> B \<noteq> F` by blast
	have "b \<noteq> e" using nullsegment3[OF `axioms` `B \<noteq> E` `seg_eq B E b e`] .
	have "e \<noteq> b" using inequalitysymmetric[OF `axioms` `b \<noteq> e`] .
	obtain w where "bet e b w \<and> seg_eq b w e b" using extensionE[OF `axioms` `e \<noteq> b` `e \<noteq> b`]  by  blast
	have "bet e b w" using `bet e b w \<and> seg_eq b w e b` by blast
	have "seg_eq b w e b" using `bet e b w \<and> seg_eq b w e b` by blast
	have "seg_eq e b E B" using doublereverse[OF `axioms` `seg_eq B E b e`] by blast
	have "seg_eq b w E B" using congruencetransitive[OF `axioms` `seg_eq b w e b` `seg_eq e b E B`] .
	have "seg_eq E B B W" using congruenceflip[OF `axioms` `seg_eq E B W B`] by blast
	have "seg_eq b w B W" using congruencetransitive[OF `axioms` `seg_eq b w E B` `seg_eq E B B W`] .
	have "seg_eq b f B F" using congruencesymmetric[OF `axioms` `seg_eq B F b f`] .
	have "seg_eq e f E F" using congruencesymmetric[OF `axioms` `seg_eq E F e f`] .
	have "seg_eq e w E W" using sumofparts[OF `axioms` `seg_eq e b E B` `seg_eq b w B W` `bet e b w` `bet E B W`] .
	have "seg_eq f w F W" using n5_lineE[OF `axioms` `seg_eq b w B W` `seg_eq e f E F` `seg_eq b f B F` `bet e b w` `bet E B W` `seg_eq e b E B`] .
	have "seg_eq e b B W" using congruencetransitive[OF `axioms` `seg_eq e b E B` `seg_eq E B B W`] .
	have "seg_eq B W b w" using congruencesymmetric[OF `axioms` `seg_eq b w B W`] .
	have "seg_eq e b b w" using congruencetransitive[OF `axioms` `seg_eq e b B W` `seg_eq B W b w`] .
	have "seg_eq e b w b" using congruenceflip[OF `axioms` `seg_eq e b b w`] by blast
	have "seg_eq e f W F" using congruencetransitive[OF `axioms` `seg_eq e f E F` `seg_eq E F W F`] .
	have "seg_eq W F w f" using doublereverse[OF `axioms` `seg_eq f w F W`] by blast
	have "seg_eq e f w f" using congruencetransitive[OF `axioms` `seg_eq e f W F` `seg_eq W F w f`] .
	have "b \<noteq> f" using raystrict[OF `axioms` `ray_on b c f`] .
	have "bet e b w \<and> seg_eq e b w b \<and> seg_eq e f w f \<and> b \<noteq> f" using `bet e b w \<and> seg_eq b w e b` `seg_eq e b w b` `seg_eq e f w f` `b \<noteq> f` by blast
	have "ang_right e b f" using rightangle_b[OF `axioms` `bet e b w` `seg_eq e b w b` `seg_eq e f w f` `b \<noteq> f`] .
	have "ray_on b f c" using ray5[OF `axioms` `ray_on b c f`] .
	have "ang_right e b c" using n8_3[OF `axioms` `ang_right e b f` `ray_on b f c`] .
	have "ang_right c b e" using n8_2[OF `axioms` `ang_right e b c`] .
	have "ray_on b e a" using ray5[OF `axioms` `ray_on b a e`] .
	have "ang_right c b a" using n8_3[OF `axioms` `ang_right c b e` `ray_on b e a`] .
	have "ang_right a b c" using n8_2[OF `axioms` `ang_right c b a`] .
	thus ?thesis by blast
qed

end