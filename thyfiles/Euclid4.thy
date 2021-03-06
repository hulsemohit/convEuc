theory Euclid4
	imports n10_12 n8_2 n8_3 Geometry Prop20 Prop22 TGflip TGsymmetric betweennotequal collinearorder congruenceflip congruencesymmetric congruencetransitive doublereverse equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric layoff layoffunique nullsegment3 ray4 rightangleNC
begin

theorem(in euclidean_geometry) Euclid4:
	assumes 
		"ang_right A B C"
		"ang_right a b c"
	shows "ang_eq A B C a b c"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" using rightangle_f[OF `ang_right A B C`]  by  blast
	have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	obtain d where "bet a b d \<and> seg_eq a b d b \<and> seg_eq a c d c \<and> b \<noteq> c" using rightangle_f[OF `ang_right a b c`]  by  blast
	have "bet a b d" using `bet a b d \<and> seg_eq a b d b \<and> seg_eq a c d c \<and> b \<noteq> c` by blast
	have "b \<noteq> c" using `bet a b d \<and> seg_eq a b d b \<and> seg_eq a c d c \<and> b \<noteq> c` by blast
	have "a \<noteq> b" using betweennotequal[OF `bet a b d`] by blast
	have "b \<noteq> a" using inequalitysymmetric[OF `a \<noteq> b`] .
	have "A \<noteq> B" using betweennotequal[OF `bet A B D`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	obtain p where "ray_on b a p \<and> seg_eq b p B A" using layoff[OF `b \<noteq> a` `B \<noteq> A`]  by  blast
	have "ray_on b a p" using `ray_on b a p \<and> seg_eq b p B A` by blast
	obtain q where "ray_on b c q \<and> seg_eq b q B C" using layoff[OF `b \<noteq> c` `B \<noteq> C`]  by  blast
	have "ray_on b c q" using `ray_on b c q \<and> seg_eq b q B C` by blast
	have "ang_right a b q" using n8_3[OF `ang_right a b c` `ray_on b c q`] .
	have "ang_right q b a" using n8_2[OF `ang_right a b q`] .
	have "ang_right q b p" using n8_3[OF `ang_right q b a` `ray_on b a p`] .
	have "ang_right p b q" using n8_2[OF `ang_right q b p`] .
	obtain r where "bet p b r \<and> seg_eq p b r b \<and> seg_eq p q r q \<and> b \<noteq> q" using rightangle_f[OF `ang_right p b q`]  by  blast
	have "seg_eq p b r b" using `bet p b r \<and> seg_eq p b r b \<and> seg_eq p q r q \<and> b \<noteq> q` by blast
	have "\<not> col p b q" using rightangleNC[OF `ang_right p b q`] .
	have "\<not> (col b q p)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col b q p))"
hence "col b q p" by blast
		have "col p b q" using collinearorder[OF `col b q p`] by blast
		show "False" using `col p b q` `\<not> col p b q` by blast
	qed
	hence "\<not> col b q p" by blast
	have "\<not> (col q p b)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col q p b))"
hence "col q p b" by blast
		have "col p b q" using collinearorder[OF `col q p b`] by blast
		show "False" using `col p b q` `\<not> col p b q` by blast
	qed
	hence "\<not> col q p b" by blast
	have "triangle p b q" using triangle_b[OF `\<not> col p b q`] .
	have "triangle b q p" using triangle_b[OF `\<not> col b q p`] .
	have "triangle q p b" using triangle_b[OF `\<not> col q p b`] .
	have "seg_sum_gt b p p q b q" using Prop20[OF `triangle p b q`] .
	have "seg_sum_gt q b b p q p" using Prop20[OF `triangle b q p`] .
	have "seg_sum_gt p q q b p b" using Prop20[OF `triangle q p b`] .
	have "seg_sum_gt b q b p q p" using TGflip[OF `seg_sum_gt q b b p q p`] by blast
	have "seg_sum_gt b q b p p q" using TGflip[OF `seg_sum_gt b q b p q p`] by blast
	have "seg_sum_gt q b p q p b" using TGsymmetric[OF `seg_sum_gt p q q b p b`] .
	have "seg_sum_gt b q p q p b" using TGflip[OF `seg_sum_gt q b p q p b`] by blast
	have "seg_sum_gt b q p q b p" using TGflip[OF `seg_sum_gt b q p q p b`] by blast
	obtain E F where "seg_eq B E b p \<and> seg_eq B F b q \<and> seg_eq E F p q \<and> ray_on B A E \<and> triangle B E F" using Prop22[OF `seg_sum_gt b q b p p q` `seg_sum_gt b q p q b p` `seg_sum_gt b p p q b q` `B \<noteq> A`]  by  blast
	have "seg_eq B E b p" using `seg_eq B E b p \<and> seg_eq B F b q \<and> seg_eq E F p q \<and> ray_on B A E \<and> triangle B E F` by blast
	have "seg_eq B F b q" using `seg_eq B E b p \<and> seg_eq B F b q \<and> seg_eq E F p q \<and> ray_on B A E \<and> triangle B E F` by blast
	have "seg_eq E F p q" using `seg_eq B E b p \<and> seg_eq B F b q \<and> seg_eq E F p q \<and> ray_on B A E \<and> triangle B E F` by blast
	have "ray_on B A E" using `seg_eq B E b p \<and> seg_eq B F b q \<and> seg_eq E F p q \<and> ray_on B A E \<and> triangle B E F` by blast
	have "A = A" using equalityreflexiveE.
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "seg_eq B E b p" using `seg_eq B E b p` .
	have "seg_eq b p B A" using `ray_on b a p \<and> seg_eq b p B A` by blast
	have "seg_eq B E B A" using congruencetransitive[OF `seg_eq B E b p` `seg_eq b p B A`] .
	have "E = A" using layoffunique[OF `ray_on B A E` `ray_on B A A` `seg_eq B E B A`] .
	have "seg_eq B A b p" using `seg_eq B E b p` `E = A` by blast
	have "seg_eq A F p q" using `seg_eq E F p q` `E = A` by blast
	have "\<not> (p = b)"
	proof (rule ccontr)
		assume "\<not> (p \<noteq> b)"
		hence "p = b" by blast
		have "col p b q" using collinear_b `p = b` by blast
		have "\<not> col p b q" using rightangleNC[OF `ang_right p b q`] .
		show "False" using `\<not> col p b q` `col p b q` by blast
	qed
	hence "p \<noteq> b" by blast
	have "bet p b r" using `bet p b r \<and> seg_eq p b r b \<and> seg_eq p q r q \<and> b \<noteq> q` by blast
	have "seg_eq r b p b" using congruencesymmetric[OF `seg_eq p b r b`] .
	have "seg_eq b r p b" using congruenceflip[OF `seg_eq r b p b`] by blast
	have "b \<noteq> p" using inequalitysymmetric[OF `p \<noteq> b`] .
	have "bet A B D" using `bet A B D` .
	have "seg_eq p b b r" using congruencesymmetric[OF `seg_eq b r p b`] .
	have "seg_eq p b A B" using doublereverse[OF `seg_eq B A b p`] by blast
	have "seg_eq b r p b" using congruencesymmetric[OF `seg_eq p b b r`] .
	have "seg_eq b r A B" using congruencetransitive[OF `seg_eq b r p b` `seg_eq p b A B`] .
	have "seg_eq A B B D" using congruenceflip[OF `seg_eq A B D B`] by blast
	have "seg_eq b r B D" using congruencetransitive[OF `seg_eq b r A B` `seg_eq A B B D`] .
	have "seg_eq b q B F" using congruencesymmetric[OF `seg_eq B F b q`] .
	have "seg_eq p q A F" using congruencesymmetric[OF `seg_eq A F p q`] .
	have "seg_eq q r F D" using n5_lineE[OF `seg_eq b r B D` `seg_eq p q A F` `seg_eq b q B F` `bet p b r` `bet A B D` `seg_eq p b A B`] .
	have "seg_eq A F p q" using `seg_eq A F p q` .
	have "seg_eq p q r q" using `bet p b r \<and> seg_eq p b r b \<and> seg_eq p q r q \<and> b \<noteq> q` by blast
	have "seg_eq A F r q" using congruencetransitive[OF `seg_eq A F p q` `seg_eq p q r q`] .
	have "seg_eq A F q r" using congruenceflip[OF `seg_eq A F r q`] by blast
	have "seg_eq A F F D" using congruencetransitive[OF `seg_eq A F q r` `seg_eq q r F D`] .
	have "seg_eq A F D F" using congruenceflip[OF `seg_eq A F F D`] by blast
	have "bet A B D" using `bet A B D` .
	have "seg_eq A B D B" using `seg_eq A B D B` .
	have "ang_right p b q" using `ang_right p b q` .
	have "b \<noteq> q" using rightangle_f[OF `ang_right a b q`] by blast
	have "B \<noteq> F" using nullsegment3[OF `b \<noteq> q` `seg_eq b q B F`] .
	have "ang_right A B F" using rightangle_b[OF `bet A B D` `seg_eq A B D B` `seg_eq A F D F` `B \<noteq> F`] .
	have "ang_right A B C" using `ang_right A B C` .
	have "seg_eq b q B F" using congruencesymmetric[OF `seg_eq B F b q`] .
	have "seg_eq b q B C" using `ray_on b c q \<and> seg_eq b q B C` by blast
	have "seg_eq B C b q" using congruencesymmetric[OF `seg_eq b q B C`] .
	have "seg_eq B C B F" using congruencetransitive[OF `seg_eq B C b q` `seg_eq b q B F`] .
	have "seg_eq A C A F" using n10_12[OF `ang_right A B C` `ang_right A B F` `seg_eq B C B F`] .
	have "F = F" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "ray_on B F F" using ray4 `F = F` `B \<noteq> F` by blast
	have "ray_on B C C" using ray4 `C = C` `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "seg_eq B A B A" using congruencereflexiveE.
	have "seg_eq B C B F" using `seg_eq B C B F` .
	have "\<not> col A B C" using rightangleNC[OF `ang_right A B C`] .
	have "ang_eq A B C A B F" using equalangles_b[OF `ray_on B A A` `ray_on B C C` `ray_on B A A` `ray_on B F F` `seg_eq B A B A` `seg_eq B C B F` `seg_eq A C A F` `\<not> col A B C`] .
	have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
	have "ang_eq A B C A B F" using equalanglestransitive[OF `ang_eq A B C A B C` `ang_eq A B C A B F`] .
	have "p = p" using equalityreflexiveE.
	have "q = q" using equalityreflexiveE.
	have "ray_on b p p" using ray4 `p = p` `b \<noteq> p` by blast
	have "ray_on b q q" using ray4 `q = q` `bet p b r \<and> seg_eq p b r b \<and> seg_eq p q r q \<and> b \<noteq> q` by blast
	have "ray_on B F F" using ray4 `F = F` `B \<noteq> F` by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "seg_eq B A b p" using congruencesymmetric[OF `seg_eq b p B A`] .
	have "seg_eq B F b q" using `seg_eq B F b q` .
	have "\<not> col A B F" using rightangleNC[OF `ang_right A B F`] .
	have "ang_eq A B F p b q" using equalangles_b[OF `ray_on B A A` `ray_on B F F` `ray_on b p p` `ray_on b q q` `seg_eq B A b p` `seg_eq B F b q` `seg_eq A F p q` `\<not> col A B F`] .
	have "ang_eq A B C p b q" using equalanglestransitive[OF `ang_eq A B C A B F` `ang_eq A B F p b q`] .
	have "ray_on b a p" using `ray_on b a p` .
	have "ray_on b c q" using `ray_on b c q` .
	have "\<not> col a b c" using rightangleNC[OF `ang_right a b c`] .
	have "ray_on b p p" using ray4 `p = p` `b \<noteq> p` by blast
	have "ray_on b q q" using ray4 `q = q` `bet p b r \<and> seg_eq p b r b \<and> seg_eq p q r q \<and> b \<noteq> q` by blast
	have "seg_eq b p b p" using congruencereflexiveE.
	have "seg_eq b q b q" using congruencereflexiveE.
	have "seg_eq p q p q" using congruencereflexiveE.
	have "ang_eq a b c p b q" using equalangles_b[OF `ray_on b a p` `ray_on b c q` `ray_on b p p` `ray_on b q q` `seg_eq b p b p` `seg_eq b q b q` `seg_eq p q p q` `\<not> col a b c`] .
	have "ang_eq p b q a b c" using equalanglessymmetric[OF `ang_eq a b c p b q`] .
	have "ang_eq A B C a b c" using equalanglestransitive[OF `ang_eq A B C p b q` `ang_eq p b q a b c`] .
	thus ?thesis by blast
qed

end