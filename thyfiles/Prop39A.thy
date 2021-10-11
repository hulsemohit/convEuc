theory Prop39A
	imports ABCequalsCBA Geometry NCdistinct NChelper NCorder Prop04 Prop10 Prop15 Prop27B Prop37 betweennotequal collinear4 collinearorder collinearparallel2 congruenceflip congruencesymmetric equalanglesNC equalanglesflip equalangleshelper equalanglessymmetric equalanglestransitive inequalitysymmetric parallelflip parallelsymmetric ray1 ray3 ray4 ray5
begin

theorem(in euclidean_geometry) Prop39A:
	assumes 
		"triangle A B C"
		"tri_eq_area A B C D B C"
		"bet A M C"
		"ray_on B D M"
	shows "parallel A D B C"
proof -
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	obtain m where "bet A m B \<and> seg_eq m A m B" using Prop10[OF `A \<noteq> B`]  by  blast
	have "bet A m B" using `bet A m B \<and> seg_eq m A m B` by blast
	have "seg_eq m A m B" using `bet A m B \<and> seg_eq m A m B` by blast
	have "col A m B" using collinear_b `bet A m B \<and> seg_eq m A m B` by blast
	have "col A B m" using collinearorder[OF `col A m B`] by blast
	have "A = A" using equalityreflexiveE.
	have "col A B A" using collinear_b `A = A` by blast
	have "A \<noteq> m" using betweennotequal[OF `bet A m B`] by blast
	have "\<not> col A m C" using NChelper[OF `\<not> col A B C` `col A B A` `col A B m` `A \<noteq> m`] .
	have "m \<noteq> C" using NCdistinct[OF `\<not> col A m C`] by blast
	have "C \<noteq> m" using inequalitysymmetric[OF `m \<noteq> C`] .
	obtain H where "bet C m H \<and> seg_eq m H m C" using extensionE[OF `C \<noteq> m` `m \<noteq> C`]  by  blast
	have "bet C m H" using `bet C m H \<and> seg_eq m H m C` by blast
	have "seg_eq m H m C" using `bet C m H \<and> seg_eq m H m C` by blast
	have "bet B m A" using betweennesssymmetryE[OF `bet A m B`] .
	have "bet C M A" using betweennesssymmetryE[OF `bet A M C`] .
	have "seg_eq m B m A" using congruencesymmetric[OF `seg_eq m A m B`] .
	have "seg_eq B m A m" using congruenceflip[OF `seg_eq m B m A`] by blast
	have "seg_eq m C m H" using congruencesymmetric[OF `seg_eq m H m C`] .
	have "\<not> (col B A H)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A H))"
hence "col B A H" by blast
		have "col A m B" using collinear_b `bet A m B \<and> seg_eq m A m B` by blast
		have "col B A m" using collinearorder[OF `col A B m`] by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
		have "col A H m" using collinear4[OF `col B A H` `col B A m` `B \<noteq> A`] .
		have "col H m A" using collinearorder[OF `col A H m`] by blast
		have "col C m H" using collinear_b `bet C m H \<and> seg_eq m H m C` by blast
		have "col H m C" using collinearorder[OF `col C m H`] by blast
		have "m \<noteq> H" using betweennotequal[OF `bet C m H`] by blast
		have "H \<noteq> m" using inequalitysymmetric[OF `m \<noteq> H`] .
		have "col m A C" using collinear4[OF `col H m A` `col H m C` `H \<noteq> m`] .
		have "col m A B" using collinearorder[OF `col A B m`] by blast
		have "A \<noteq> m" using betweennotequal[OF `bet A m B`] by blast
		have "m \<noteq> A" using inequalitysymmetric[OF `A \<noteq> m`] .
		have "col A B C" using collinear4[OF `col m A B` `col m A C` `m \<noteq> A`] .
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A H" by blast
	obtain E where "bet B M E \<and> bet H A E" using Euclid5E[OF `bet C m H` `bet B m A` `bet C M A` `seg_eq B m A m` `seg_eq m C m H`]  by  blast
	have "bet H A E" using `bet B M E \<and> bet H A E` by blast
	have "bet H m C" using betweennesssymmetryE[OF `bet C m H`] .
	have "col C m H" using collinear_b `bet C m H \<and> seg_eq m H m C` by blast
	have "col m C H" using collinearorder[OF `col C m H`] by blast
	have "m = m" using equalityreflexiveE.
	have "col m C m" using collinear_b `m = m` by blast
	have "\<not> col m C A" using NCorder[OF `\<not> col A m C`] by blast
	have "m \<noteq> H" using betweennotequal[OF `bet C m H`] by blast
	have "\<not> col m H A" using NChelper[OF `\<not> col m C A` `col m C m` `col m C H` `m \<noteq> H`] .
	have "\<not> col A m H" using NCorder[OF `\<not> col m H A`] by blast
	have "ang_eq A m H C m B" using Prop15[OF `bet A m B` `bet H m C` `\<not> col A m H`] by blast
	have "\<not> col H m A" using NCorder[OF `\<not> col A m H`] by blast
	have "col A m B" using collinear_b `bet A m B \<and> seg_eq m A m B` by blast
	have "col A B m" using collinearorder[OF `col A m B`] by blast
	have "B = B" using equalityreflexiveE.
	have "col A B B" using collinear_b `B = B` by blast
	have "m \<noteq> B" using betweennotequal[OF `bet A m B`] by blast
	have "\<not> col m B C" using NChelper[OF `\<not> col A B C` `col A B m` `col A B B` `m \<noteq> B`] .
	have "ang_eq H m A A m H" using ABCequalsCBA[OF `\<not> col H m A`] .
	have "ang_eq H m A C m B" using equalanglestransitive[OF `ang_eq H m A A m H` `ang_eq A m H C m B`] .
	have "seg_eq m H m C" using `seg_eq m H m C` .
	have "seg_eq m B m A" using `seg_eq m B m A` .
	have "seg_eq m A m B" using congruencesymmetric[OF `seg_eq m B m A`] .
	have "ang_eq m H A m C B" using Prop04[OF `seg_eq m H m C` `seg_eq m A m B` `ang_eq H m A C m B`] by blast
	have "B = B" using equalityreflexiveE.
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "ray_on C m H" using ray4 `bet C m H \<and> seg_eq m H m C` `C \<noteq> m` by blast
	have "ang_eq m H A H C B" using equalangleshelper[OF `ang_eq m H A m C B` `ray_on C m H` `ray_on C B B`] .
	have "ang_eq H C B m H A" using equalanglessymmetric[OF `ang_eq m H A H C B`] .
	have "A = A" using equalityreflexiveE.
	have "H \<noteq> A" using NCdistinct[OF `\<not> col A m H`] by blast
	have "ray_on H A A" using ray4 `A = A` `H \<noteq> A` by blast
	have "bet H m C" using betweennesssymmetryE[OF `bet C m H`] .
	have "H \<noteq> m" using betweennotequal[OF `bet H m C`] by blast
	have "ray_on H m C" using ray4 `bet H m C` `H \<noteq> m` by blast
	have "ang_eq H C B C H A" using equalangleshelper[OF `ang_eq H C B m H A` `ray_on H m C` `ray_on H A A`] .
	have "ang_eq C H A H C B" using equalanglessymmetric[OF `ang_eq H C B C H A`] .
	have "ang_eq A H C B C H" using equalanglesflip[OF `ang_eq C H A H C B`] .
	have "\<not> col B C H" using equalanglesNC[OF `ang_eq A H C B C H`] .
	have "ang_eq B C H H C B" using ABCequalsCBA[OF `\<not> col B C H`] .
	have "ang_eq A H C H C B" using equalanglestransitive[OF `ang_eq A H C B C H` `ang_eq B C H H C B`] .
	have "col C m H" using collinear_b `bet C m H \<and> seg_eq m H m C` by blast
	have "col H C m" using collinearorder[OF `col C m H`] by blast
	have "col H m C" using collinearorder[OF `col C m H`] by blast
	have "H = H" using equalityreflexiveE.
	have "col H m H" using collinear_b `H = H` by blast
	have "\<not> col H m A" using `\<not> col H m A` .
	have "H \<noteq> C" using betweennotequal[OF `bet H m C`] by blast
	have "\<not> col H C A" using NChelper[OF `\<not> col H m A` `col H m H` `col H m C` `H \<noteq> C`] .
	have "oppo_side A H C B" using oppositeside_b[OF `bet A m B` `col H C m` `\<not> col H C A`] .
	have "parallel A H C B" using Prop27B[OF `ang_eq A H C H C B` `oppo_side A H C B`] .
	have "col H A E" using collinear_b `bet B M E \<and> bet H A E` by blast
	have "col A H E" using collinearorder[OF `col H A E`] by blast
	have "col A H A" using collinear_b `A = A` by blast
	have "A \<noteq> E" using betweennotequal[OF `bet H A E`] by blast
	have "parallel C B A H" using parallelsymmetric[OF `parallel A H C B`] .
	have "parallel C B A E" using collinearparallel2[OF `parallel C B A H` `col A H A` `col A H E` `A \<noteq> E`] .
	have "parallel A E C B" using parallelsymmetric[OF `parallel C B A E`] .
	have "parallel A E B C" using parallelflip[OF `parallel A E C B`] by blast
	have "tri_eq_area A B C E B C" using Prop37[OF `parallel A E B C`] .
	have "tri_eq_area D B C A B C" using ETsymmetricE[OF `tri_eq_area A B C D B C`] .
	have "tri_eq_area D B C E B C" using ETtransitiveE[OF `tri_eq_area D B C A B C` `tri_eq_area A B C E B C`] .
	have "ray_on B D M" using `ray_on B D M` .
	have "ray_on B M D" using ray5[OF `ray_on B D M`] .
	have "bet B M E" using `bet B M E \<and> bet H A E` by blast
	have "B \<noteq> M" using betweennotequal[OF `bet B M E`] by blast
	have "ray_on B M E" using ray4 `bet B M E \<and> bet H A E` `B \<noteq> M` by blast
	have "ray_on B D E" using ray3[OF `ray_on B M D` `ray_on B M E`] .
	have "bet B E D \<or> D = E \<or> bet B D E" using ray1[OF `ray_on B D E`] .
	consider "bet B E D"|"D = E"|"bet B D E" using `bet B E D \<or> D = E \<or> bet B D E`  by blast
	hence "parallel A D B C"
	proof (cases)
		assume "bet B E D"
		have "\<not> (\<not> (parallel A D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (parallel A D B C)))"
hence "\<not> (parallel A D B C)" by blast
			have "\<not> (tri_eq_area D B C E B C)" using deZolt1E[OF `bet B E D`] .
			show "False" using `\<not> (tri_eq_area D B C E B C)` `tri_eq_area D B C E B C` by blast
		qed
		hence "parallel A D B C" by blast
		thus ?thesis by blast
	next
		assume "D = E"
		have "parallel A D B C" using `parallel A E B C` `D = E` by blast
		thus ?thesis by blast
	next
		assume "bet B D E"
		have "\<not> (\<not> (parallel A D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (parallel A D B C)))"
hence "\<not> (parallel A D B C)" by blast
			have "\<not> (tri_eq_area E B C D B C)" using deZolt1E[OF `bet B D E`] .
			have "tri_eq_area E B C D B C" using ETsymmetricE[OF `tri_eq_area D B C E B C`] .
			show "False" using `tri_eq_area E B C D B C` `\<not> (tri_eq_area E B C D B C)` by blast
		qed
		hence "parallel A D B C" by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end