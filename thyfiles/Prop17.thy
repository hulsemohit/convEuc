theory Prop17
	imports ABCequalsCBA Geometry NCdistinct NChelper NCorder Prop16 angleorderrespectscongruence2 betweennotequal collinearorder crossbar equalangleshelper equalanglesreflexive equalanglestransitive inequalitysymmetric ray2 ray4 ray5 rayimpliescollinear
begin

theorem Prop17:
	assumes "axioms"
		"triangle A B C"
	shows "\<exists> E. area_sum_eq A B C B C A E C B"
proof -
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	obtain D where "bet B C D \<and> seg_eq C D B C" using extensionE[OF `axioms` `B \<noteq> C` `B \<noteq> C`]  by  blast
	have "bet B C D" using `bet B C D \<and> seg_eq C D B C` by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col B C D" using collinear_b `axioms` `bet B C D \<and> seg_eq C D B C` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B C B" using collinear_b `axioms` `B = B` by blast
	have "B \<noteq> D" using betweennotequal[OF `axioms` `bet B C D`] by blast
	have "\<not> col B D A" using NChelper[OF `axioms` `\<not> col B C A` `col B C B` `col B C D` `B \<noteq> D`] .
	have "\<not> col A D B" using NCorder[OF `axioms` `\<not> col B D A`] by blast
	have "ang_lt C B A A C D" using Prop16[OF `axioms` `triangle A B C` `bet B C D`] by blast
	have "ang_eq A B C C B A" using ABCequalsCBA[OF `axioms` `\<not> col A B C`] .
	have "ang_lt A B C A C D" using angleorderrespectscongruence2[OF `axioms` `ang_lt C B A A C D` `ang_eq A B C C B A`] .
	obtain a d e where "bet a e d \<and> ray_on C A a \<and> ray_on C D d \<and> ang_eq A B C A C e" using anglelessthan_f[OF `axioms` `ang_lt A B C A C D`]  by  blast
	have "bet a e d" using `bet a e d \<and> ray_on C A a \<and> ray_on C D d \<and> ang_eq A B C A C e` by blast
	have "ray_on C A a" using `bet a e d \<and> ray_on C A a \<and> ray_on C D d \<and> ang_eq A B C A C e` by blast
	have "ray_on C D d" using `bet a e d \<and> ray_on C A a \<and> ray_on C D d \<and> ang_eq A B C A C e` by blast
	have "ang_eq A B C A C e" using `bet a e d \<and> ray_on C A a \<and> ray_on C D d \<and> ang_eq A B C A C e` by blast
	have "ray_on C a A" using ray5[OF `axioms` `ray_on C A a`] .
	have "ray_on C d D" using ray5[OF `axioms` `ray_on C D d`] .
	have "col B C D" using collinear_b `axioms` `bet B C D \<and> seg_eq C D B C` by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col B C C" using collinear_b `axioms` `C = C` by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet B C D`] by blast
	have "\<not> col C D A" using NChelper[OF `axioms` `\<not> col B C A` `col B C C` `col B C D` `C \<noteq> D`] .
	have "col C D C" using collinear_b `axioms` `C = C` by blast
	have "col C D d" using rayimpliescollinear[OF `axioms` `ray_on C D d`] .
	have "C \<noteq> d" using ray2[OF `axioms` `ray_on C d D`] .
	have "\<not> col C d A" using NChelper[OF `axioms` `\<not> col C D A` `col C D C` `col C D d` `C \<noteq> d`] .
	have "\<not> col C A d" using NCorder[OF `axioms` `\<not> col C d A`] by blast
	have "col C A a" using rayimpliescollinear[OF `axioms` `ray_on C A a`] .
	have "col C A C" using collinear_b `axioms` `C = C` by blast
	have "C \<noteq> a" using ray2[OF `axioms` `ray_on C a A`] .
	have "\<not> col C a d" using NChelper[OF `axioms` `\<not> col C A d` `col C A C` `col C A a` `C \<noteq> a`] .
	have "\<not> col a C d" using NCorder[OF `axioms` `\<not> col C a d`] by blast
	have "\<not> col D A C" using NCorder[OF `axioms` `\<not> col C D A`] by blast
	have "triangle a C d" using triangle_b[OF `axioms` `\<not> col a C d`] .
	obtain E where "ray_on C e E \<and> bet A E D" using crossbar[OF `axioms` `triangle a C d` `bet a e d` `ray_on C a A` `ray_on C d D`]  by  blast
	have "ray_on C e E" using `ray_on C e E \<and> bet A E D` by blast
	have "ray_on C E e" using ray5[OF `axioms` `ray_on C e E`] .
	have "bet A E D" using `ray_on C e E \<and> bet A E D` by blast
	have "col A E D" using collinear_b `axioms` `ray_on C e E \<and> bet A E D` by blast
	have "col D A E" using collinearorder[OF `axioms` `col A E D`] by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "col D A A" using collinear_b `axioms` `A = A` by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A E D`] by blast
	have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
	have "\<not> col E A C" using NChelper[OF `axioms` `\<not> col D A C` `col D A E` `col D A A` `E \<noteq> A`] .
	have "\<not> col A C E" using NCorder[OF `axioms` `\<not> col E A C`] by blast
	have "\<not> col C E A" using NCorder[OF `axioms` `\<not> col A C E`] by blast
	have "col C E e" using rayimpliescollinear[OF `axioms` `ray_on C E e`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col C E C" using collinear_b `axioms` `C = C` by blast
	have "C \<noteq> e" using ray2[OF `axioms` `ray_on C e E`] .
	have "\<not> col C e A" using NChelper[OF `axioms` `\<not> col C E A` `col C E C` `col C E e` `C \<noteq> e`] .
	have "\<not> col A C e" using NCorder[OF `axioms` `\<not> col C e A`] by blast
	have "col C A a" using rayimpliescollinear[OF `axioms` `ray_on C A a`] .
	have "col A C a" using collinearorder[OF `axioms` `col C A a`] by blast
	have "col A C C" using collinear_b `axioms` `C = C` by blast
	have "C \<noteq> a" using ray2[OF `axioms` `ray_on C a A`] .
	have "a \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> a`] .
	have "\<not> col a C e" using NChelper[OF `axioms` `\<not> col A C e` `col A C a` `col A C C` `a \<noteq> C`] .
	have "\<not> col E C A" using NCorder[OF `axioms` `\<not> col A C E`] by blast
	have "ang_eq a C e a C e" using equalanglesreflexive[OF `axioms` `\<not> col a C e`] .
	have "ang_eq a C e A C E" using equalangleshelper[OF `axioms` `ang_eq a C e a C e` `ray_on C a A` `ray_on C e E`] .
	have "e = e" using equalityreflexiveE[OF `axioms`] .
	have "C \<noteq> e" using ray2[OF `axioms` `ray_on C e E`] .
	have "ray_on C e e" using ray4 `axioms` `e = e` `C \<noteq> e` by blast
	have "ang_eq A C e A C e" using equalanglesreflexive[OF `axioms` `\<not> col A C e`] .
	have "ang_eq A C e a C e" using equalangleshelper[OF `axioms` `ang_eq A C e A C e` `ray_on C A a` `ray_on C e e`] .
	have "ang_eq A B C a C e" using equalanglestransitive[OF `axioms` `ang_eq A B C A C e` `ang_eq A C e a C e`] .
	have "ang_eq A B C A C E" using equalanglestransitive[OF `axioms` `ang_eq A B C a C e` `ang_eq a C e A C E`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	obtain F where "bet A F C \<and> bet B F E" using Pasch_innerE[OF `axioms` `bet A E D` `bet B C D` `\<not> col A D B`]  by  blast
	have "bet A F C" using `bet A F C \<and> bet B F E` by blast
	have "bet B F E" using `bet A F C \<and> bet B F E` by blast
	have "\<not> col A C B" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col A F C" using collinear_b `axioms` `bet A F C \<and> bet B F E` by blast
	have "col A C F" using collinearorder[OF `axioms` `col A F C`] by blast
	have "col A C C" using collinear_b `axioms` `C = C` by blast
	have "F \<noteq> C" using betweennotequal[OF `axioms` `bet A F C`] by blast
	have "\<not> col F C B" using NChelper[OF `axioms` `\<not> col A C B` `col A C F` `col A C C` `F \<noteq> C`] .
	have "\<not> col B C F" using NCorder[OF `axioms` `\<not> col F C B`] by blast
	have "bet E F B" using betweennesssymmetryE[OF `axioms` `bet B F E`] .
	have "ang_eq A C E E C A" using ABCequalsCBA[OF `axioms` `\<not> col A C E`] .
	have "ang_eq A B C E C A" using equalanglestransitive[OF `axioms` `ang_eq A B C A C E` `ang_eq A C E E C A`] .
	have "ang_eq E C A E C A" using equalanglesreflexive[OF `axioms` `\<not> col E C A`] .
	have "bet C F A" using betweennesssymmetryE[OF `axioms` `bet A F C`] .
	have "C \<noteq> F" using betweennotequal[OF `axioms` `bet C F A`] by blast
	have "ray_on C F A" using ray4 `axioms` `bet C F A` `C \<noteq> F` by blast
	have "ray_on C A F" using ray5[OF `axioms` `ray_on C F A`] .
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "C \<noteq> E" using NCdistinct[OF `axioms` `\<not> col A C E`] by blast
	have "ray_on C E E" using ray4 `axioms` `E = E` `C \<noteq> E` by blast
	have "ang_eq E C A E C F" using equalangleshelper[OF `axioms` `ang_eq E C A E C A` `ray_on C E E` `ray_on C A F`] .
	have "ang_eq A B C E C F" using equalanglestransitive[OF `axioms` `ang_eq A B C E C A` `ang_eq E C A E C F`] .
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "ang_eq B C A B C A" using equalanglesreflexive[OF `axioms` `\<not> col B C A`] .
	have "C \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "ang_eq B C A B C F" using equalangleshelper[OF `axioms` `ang_eq B C A B C A` `ray_on C B B` `ray_on C A F`] .
	have "ang_eq B C F F C B" using ABCequalsCBA[OF `axioms` `\<not> col B C F`] .
	have "ang_eq B C A F C B" using equalanglestransitive[OF `axioms` `ang_eq B C A B C F` `ang_eq B C F F C B`] .
	have "area_sum_eq A B C B C A E C B" using anglesum_b[OF `axioms` `ang_eq A B C E C F` `ang_eq B C A F C B` `bet E F B`] .
	thus ?thesis by blast
qed

end