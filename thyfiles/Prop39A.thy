theory Prop39A
	imports Axioms Definitions Theorems
begin

theorem Prop39A:
	assumes: `axioms`
		"triangle A B C"
		"tri_eq_area A B C D B C"
		"bet A M C"
		"ray_on B D M"
	shows: "parallel A D B C"
proof -
	have "\<not> col A B C" sorry
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	obtain m where "bet A m B \<and> seg_eq m A m B" using Prop10[OF `axioms` `A \<noteq> B`]  by  blast
	have "bet A m B" using `bet A m B \<and> seg_eq m A m B` by blast
	have "seg_eq m A m B" using `bet A m B \<and> seg_eq m A m B` by blast
	have "col A m B" using col_b `axioms` `bet A m B \<and> seg_eq m A m B` by blast
	have "col A B m" using collinearorder[OF `axioms` `col A m B`] by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "col A B A" using col_b `axioms` `A = A` by blast
	have "A \<noteq> m" using betweennotequal[OF `axioms` `bet A m B`] by blast
	have "\<not> col A m C" using NChelper[OF `axioms` `\<not> col A B C` `col A B A` `col A B m` `A \<noteq> m`] .
	have "m \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A m C`] by blast
	have "C \<noteq> m" using inequalitysymmetric[OF `axioms` `m \<noteq> C`] .
	obtain H where "bet C m H \<and> seg_eq m H m C" using extensionE[OF `axioms` `C \<noteq> m` `m \<noteq> C`]  by  blast
	have "bet C m H" using `bet C m H \<and> seg_eq m H m C` by blast
	have "seg_eq m H m C" using `bet C m H \<and> seg_eq m H m C` by blast
	have "bet B m A" using betweennesssymmetryE[OF `axioms` `bet A m B`] .
	have "bet C M A" using betweennesssymmetryE[OF `axioms` `bet A M C`] .
	have "seg_eq m B m A" using congruencesymmetric[OF `axioms` `seg_eq m A m B`] .
	have "seg_eq B m A m" using congruenceflip[OF `axioms` `seg_eq m B m A`] by blast
	have "seg_eq m C m H" using congruencesymmetric[OF `axioms` `seg_eq m H m C`] .
	have "\<not> (col B A H)"
	proof (rule ccontr)
		assume "col B A H"
		have "col A m B" using col_b `axioms` `bet A m B \<and> seg_eq m A m B` by blast
		have "col B A m" using collinearorder[OF `axioms` `col A B m`] by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
		have "col A H m" using collinear4[OF `axioms` `col B A H` `col B A m` `B \<noteq> A`] .
		have "col H m A" using collinearorder[OF `axioms` `col A H m`] by blast
		have "col C m H" using col_b `axioms` `bet C m H \<and> seg_eq m H m C` by blast
		have "col H m C" using collinearorder[OF `axioms` `col C m H`] by blast
		have "m \<noteq> H" using betweennotequal[OF `axioms` `bet C m H`] by blast
		have "H \<noteq> m" using inequalitysymmetric[OF `axioms` `m \<noteq> H`] .
		have "col m A C" using collinear4[OF `axioms` `col H m A` `col H m C` `H \<noteq> m`] .
		have "col m A B" using collinearorder[OF `axioms` `col A B m`] by blast
		have "A \<noteq> m" using betweennotequal[OF `axioms` `bet A m B`] by blast
		have "m \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> m`] .
		have "col A B C" using collinear4[OF `axioms` `col m A B` `col m A C` `m \<noteq> A`] .
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A H" by blast
	obtain E where "bet B M E \<and> bet H A E" using Euclid5E[OF `axioms` `bet C m H` `bet B m A` `bet C M A` `seg_eq B m A m` `seg_eq m C m H`]  by  blast
	have "bet H A E" using `bet B M E \<and> bet H A E` by blast
	have "bet H m C" using betweennesssymmetryE[OF `axioms` `bet C m H`] .
	have "col C m H" using col_b `axioms` `bet C m H \<and> seg_eq m H m C` by blast
	have "col m C H" using collinearorder[OF `axioms` `col C m H`] by blast
	have "m = m" using equalityreflexiveE[OF `axioms`] .
	have "col m C m" using col_b `axioms` `m = m` by blast
	have "\<not> col m C A" using NCorder[OF `axioms` `\<not> col A m C`] by blast
	have "m \<noteq> H" using betweennotequal[OF `axioms` `bet C m H`] by blast
	have "\<not> col m H A" using NChelper[OF `axioms` `\<not> col m C A` `col m C m` `col m C H` `m \<noteq> H`] .
	have "\<not> col A m H" using NCorder[OF `axioms` `\<not> col m H A`] by blast
	have "ang_eq A m H C m B" using Prop15[OF `axioms` `bet A m B` `bet H m C` `\<not> col A m H`] by blast
	have "\<not> col H m A" using NCorder[OF `axioms` `\<not> col A m H`] by blast
	have "col A m B" using col_b `axioms` `bet A m B \<and> seg_eq m A m B` by blast
	have "col A B m" using collinearorder[OF `axioms` `col A m B`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col A B B" using col_b `axioms` `B = B` by blast
	have "m \<noteq> B" using betweennotequal[OF `axioms` `bet A m B`] by blast
	have "\<not> col m B C" using NChelper[OF `axioms` `\<not> col A B C` `col A B m` `col A B B` `m \<noteq> B`] .
	have "ang_eq H m A A m H" using ABCequalsCBA[OF `axioms` `\<not> col H m A`] .
	have "ang_eq H m A C m B" using equalanglestransitive[OF `axioms` `ang_eq H m A A m H` `ang_eq A m H C m B`] .
	have "seg_eq m H m C" using `seg_eq m H m C` .
	have "seg_eq m B m A" using `seg_eq m B m A` .
	have "seg_eq m A m B" using congruencesymmetric[OF `axioms` `seg_eq m B m A`] .
	have "ang_eq m H A m C B" using Prop04[OF `axioms` `seg_eq m H m C` `seg_eq m A m B` `ang_eq H m A C m B`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "ray_on C m H" using ray4 `axioms` `bet C m H \<and> seg_eq m H m C` `C \<noteq> m` by blast
	have "ang_eq m H A H C B" using equalangleshelper[OF `axioms` `ang_eq m H A m C B` `ray_on C m H` `ray_on C B B`] .
	have "ang_eq H C B m H A" using equalanglessymmetric[OF `axioms` `ang_eq m H A H C B`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "H \<noteq> A" using NCdistinct[OF `axioms` `\<not> col A m H`] by blast
	have "ray_on H A A" using ray4 `axioms` `A = A` `H \<noteq> A` by blast
	have "bet H m C" using betweennesssymmetryE[OF `axioms` `bet C m H`] .
	have "H \<noteq> m" using betweennotequal[OF `axioms` `bet H m C`] by blast
	have "ray_on H m C" using ray4 `axioms` `bet H m C` `H \<noteq> m` by blast
	have "ang_eq H C B C H A" using equalangleshelper[OF `axioms` `ang_eq H C B m H A` `ray_on H m C` `ray_on H A A`] .
	have "ang_eq C H A H C B" using equalanglessymmetric[OF `axioms` `ang_eq H C B C H A`] .
	have "ang_eq A H C B C H" using equalanglesflip[OF `axioms` `ang_eq C H A H C B`] .
	have "\<not> col B C H" using equalanglesNC[OF `axioms` `ang_eq A H C B C H`] .
	have "ang_eq B C H H C B" using ABCequalsCBA[OF `axioms` `\<not> col B C H`] .
	have "ang_eq A H C H C B" using equalanglestransitive[OF `axioms` `ang_eq A H C B C H` `ang_eq B C H H C B`] .
	have "col C m H" using col_b `axioms` `bet C m H \<and> seg_eq m H m C` by blast
	have "col H C m" using collinearorder[OF `axioms` `col C m H`] by blast
	have "col H m C" using collinearorder[OF `axioms` `col C m H`] by blast
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col H m H" using col_b `axioms` `H = H` by blast
	have "\<not> col H m A" using `\<not> col H m A` .
	have "H \<noteq> C" using betweennotequal[OF `axioms` `bet H m C`] by blast
	have "\<not> col H C A" using NChelper[OF `axioms` `\<not> col H m A` `col H m H` `col H m C` `H \<noteq> C`] .
	have "oppo_side A H C B" sorry
	have "parallel A H C B" using Prop27B[OF `axioms` `ang_eq A H C H C B` `oppo_side A H C B`] .
	have "col H A E" using col_b `axioms` `bet B M E \<and> bet H A E` by blast
	have "col A H E" using collinearorder[OF `axioms` `col H A E`] by blast
	have "col A H A" using col_b `axioms` `A = A` by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet H A E`] by blast
	have "parallel C B A H" using parallelsymmetric[OF `axioms` `parallel A H C B`] .
	have "parallel C B A E" using collinearparallel2[OF `axioms` `parallel C B A H` `col A H A` `col A H E` `A \<noteq> E`] .
	have "parallel A E C B" using parallelsymmetric[OF `axioms` `parallel C B A E`] .
	have "parallel A E B C" using parallelflip[OF `axioms` `parallel A E C B`] by blast
	have "tri_eq_area A B C E B C" using Prop37[OF `axioms` `parallel A E B C`] .
	have "tri_eq_area D B C A B C" using ETsymmetricE[OF `axioms` `tri_eq_area A B C D B C`] .
	have "tri_eq_area D B C E B C" using ETtransitiveE[OF `axioms` `tri_eq_area D B C A B C` `tri_eq_area A B C E B C`] .
	have "ray_on B D M" using `ray_on B D M` .
	have "ray_on B M D" using ray5[OF `axioms` `ray_on B D M`] .
	have "bet B M E" using `bet B M E \<and> bet H A E` by blast
	have "B \<noteq> M" using betweennotequal[OF `axioms` `bet B M E`] by blast
	have "ray_on B M E" using ray4 `axioms` `bet B M E \<and> bet H A E` `B \<noteq> M` by blast
	have "ray_on B D E" using ray3[OF `axioms` `ray_on B M D` `ray_on B M E`] .
	have "bet B E D \<or> D = E \<or> bet B D E" using ray1[OF `axioms` `ray_on B D E`] .
	consider "bet B E D"|"D = E"|"bet B D E" using `bet B E D \<or> D = E \<or> bet B D E`  by blast
	hence parallel A D B C
	proof (cases)
		case 1
		have "parallel A D B C"
		proof (rule ccontr)
			assume "\<not> (parallel A D B C)"
			have "\<not> (tri_eq_area D B C E B C)" using deZolt1E[OF `axioms` `bet B E D`] .
			show "False" using `\<not> (tri_eq_area D B C E B C)` `tri_eq_area D B C E B C` by blast
		qed
		hence "parallel A D B C" by blast
	next
		case 2
		have "parallel A D B C" sorry
	next
		case 3
		have "parallel A D B C"
		proof (rule ccontr)
			assume "\<not> (parallel A D B C)"
			have "\<not> (tri_eq_area E B C D B C)" using deZolt1E[OF `axioms` `bet B D E`] .
			have "tri_eq_area E B C D B C" using ETsymmetricE[OF `axioms` `tri_eq_area D B C E B C`] .
			show "False" using `tri_eq_area E B C D B C` `\<not> (tri_eq_area E B C D B C)` by blast
		qed
		hence "parallel A D B C" by blast
	next
	thus ?thesis by blast
qed

end