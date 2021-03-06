theory Prop39
	imports Geometry NCdistinct NCorder Prop07 Prop26A Prop39A angletrichotomy2 crossbar2 equalanglesflip equalanglessymmetric inequalitysymmetric parallelflip ray4 samesideflip samesidesymmetric
begin

theorem(in euclidean_geometry) Prop39:
	assumes 
		"triangle A B C"
		"triangle D B C"
		"same_side A D B C"
		"tri_eq_area A B C D B C"
		"A \<noteq> D"
	shows "parallel A D B C"
proof -
	have "same_side D A B C" using samesidesymmetric[OF `same_side A D B C`] by blast
	have "same_side A D C B" using samesideflip[OF `same_side A D B C`] .
	have "same_side D A C B" using samesidesymmetric[OF `same_side A D B C`] by blast
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> col D B C" using triangle_f[OF `triangle D B C`] .
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "B \<noteq> D" using NCdistinct[OF `\<not> col D B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> A" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> D" using NCdistinct[OF `\<not> col D B C`] by blast
	have "A = A" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "D = D" using equalityreflexiveE.
	have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "ray_on B D D" using ray4 `D = D` `B \<noteq> D` by blast
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "ray_on C A A" using ray4 `A = A` `C \<noteq> A` by blast
	have "ray_on C D D" using ray4 `D = D` `C \<noteq> D` by blast
	have "\<not> (\<not> (parallel A D B C))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (parallel A D B C)))"
hence "\<not> (parallel A D B C)" by blast
		have "\<not> (ang_lt C B D C B A)"
		proof (rule ccontr)
			assume "\<not> (\<not> (ang_lt C B D C B A))"
hence "ang_lt C B D C B A" by blast
			obtain M where "bet A M C \<and> ray_on B D M" using crossbar2[OF `ang_lt C B D C B A` `same_side D A B C` `ray_on B C C` `ray_on B A A`]  by  blast
			have "bet A M C" using `bet A M C \<and> ray_on B D M` by blast
			have "ray_on B D M" using `bet A M C \<and> ray_on B D M` by blast
			have "parallel A D B C" using Prop39A[OF `triangle A B C` `tri_eq_area A B C D B C` `bet A M C` `ray_on B D M`] .
			show "False" using `parallel A D B C` `\<not> (parallel A D B C)` by blast
		qed
		hence "\<not> (ang_lt C B D C B A)" by blast
		have "\<not> (ang_lt C B A C B D)"
		proof (rule ccontr)
			assume "\<not> (\<not> (ang_lt C B A C B D))"
hence "ang_lt C B A C B D" by blast
			obtain M where "bet D M C \<and> ray_on B A M" using crossbar2[OF `ang_lt C B A C B D` `same_side A D B C` `ray_on B C C` `ray_on B D D`]  by  blast
			have "bet D M C" using `bet D M C \<and> ray_on B A M` by blast
			have "ray_on B A M" using `bet D M C \<and> ray_on B A M` by blast
			have "tri_eq_area D B C A B C" using ETsymmetricE[OF `tri_eq_area A B C D B C`] .
			have "parallel D A B C" using Prop39A[OF `triangle D B C` `tri_eq_area D B C A B C` `bet D M C` `ray_on B A M`] .
			have "parallel A D B C" using parallelflip[OF `parallel D A B C`] by blast
			show "False" using `parallel A D B C` `\<not> (parallel A D B C)` by blast
		qed
		hence "\<not> (ang_lt C B A C B D)" by blast
		have "\<not> (\<not> (ang_eq C B D C B A))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ang_eq C B D C B A)))"
hence "\<not> (ang_eq C B D C B A)" by blast
			have "\<not> col C B A" using NCorder[OF `\<not> col A B C`] by blast
			have "\<not> col C B D" using NCorder[OF `\<not> col D B C`] by blast
			have "ang_lt C B D C B A" using angletrichotomy2[OF `\<not> col C B D` `\<not> col C B A` `\<not> (ang_eq C B D C B A)` `\<not> (ang_lt C B A C B D)`] .
			show "False" using `ang_lt C B D C B A` `\<not> (ang_lt C B D C B A)` by blast
		qed
		hence "ang_eq C B D C B A" by blast
		have "\<not> col A C B" using NCorder[OF `\<not> col A B C`] by blast
		have "triangle A C B" using triangle_b[OF `\<not> col A C B`] .
		have "\<not> col D C B" using NCorder[OF `\<not> col D B C`] by blast
		have "triangle D C B" using triangle_b[OF `\<not> col D C B`] .
		have "same_side A D C B" using samesideflip[OF `same_side A D B C`] .
		have "tri_eq_area A B C D C B" using ETpermutationE[OF `tri_eq_area A B C D B C`] by blast
		have "tri_eq_area D C B A B C" using ETsymmetricE[OF `tri_eq_area A B C D C B`] .
		have "tri_eq_area D C B A C B" using ETpermutationE[OF `tri_eq_area D C B A B C`] by blast
		have "tri_eq_area A C B D C B" using ETsymmetricE[OF `tri_eq_area D C B A C B`] .
		have "\<not> (ang_lt B C D B C A)"
		proof (rule ccontr)
			assume "\<not> (\<not> (ang_lt B C D B C A))"
hence "ang_lt B C D B C A" by blast
			obtain M where "bet A M B \<and> ray_on C D M" using crossbar2[OF `ang_lt B C D B C A` `same_side D A C B` `ray_on C B B` `ray_on C A A`]  by  blast
			have "bet A M B" using `bet A M B \<and> ray_on C D M` by blast
			have "ray_on C D M" using `bet A M B \<and> ray_on C D M` by blast
			have "triangle A C B" using `triangle A C B` .
			have "parallel A D C B" using Prop39A[OF `triangle A C B` `tri_eq_area A C B D C B` `bet A M B` `ray_on C D M`] .
			have "parallel A D B C" using parallelflip[OF `parallel A D C B`] by blast
			show "False" using `parallel A D B C` `\<not> (parallel A D B C)` by blast
		qed
		hence "\<not> (ang_lt B C D B C A)" by blast
		have "\<not> (ang_lt B C A B C D)"
		proof (rule ccontr)
			assume "\<not> (\<not> (ang_lt B C A B C D))"
hence "ang_lt B C A B C D" by blast
			obtain M where "bet D M B \<and> ray_on C A M" using crossbar2[OF `ang_lt B C A B C D` `same_side A D C B` `ray_on C B B` `ray_on C D D`]  by  blast
			have "bet D M B" using `bet D M B \<and> ray_on C A M` by blast
			have "ray_on C A M" using `bet D M B \<and> ray_on C A M` by blast
			have "tri_eq_area D C B A C B" using ETsymmetricE[OF `tri_eq_area A C B D C B`] .
			have "parallel D A C B" using Prop39A[OF `triangle D C B` `tri_eq_area D C B A C B` `bet D M B` `ray_on C A M`] .
			have "parallel A D B C" using parallelflip[OF `parallel D A C B`] by blast
			show "False" using `parallel A D B C` `\<not> (parallel A D B C)` by blast
		qed
		hence "\<not> (ang_lt B C A B C D)" by blast
		have "\<not> (\<not> (ang_eq B C D B C A))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ang_eq B C D B C A)))"
hence "\<not> (ang_eq B C D B C A)" by blast
			have "\<not> col B C A" using NCorder[OF `\<not> col A B C`] by blast
			have "\<not> col B C D" using NCorder[OF `\<not> col D B C`] by blast
			have "ang_lt B C D B C A" using angletrichotomy2[OF `\<not> col B C D` `\<not> col B C A` `\<not> (ang_eq B C D B C A)` `\<not> (ang_lt B C A B C D)`] .
			show "False" using `ang_lt B C D B C A` `\<not> (ang_lt B C D B C A)` by blast
		qed
		hence "ang_eq B C D B C A" by blast
		have "ang_eq B C A B C D" using equalanglessymmetric[OF `ang_eq B C D B C A`] .
		have "seg_eq B C B C" using congruencereflexiveE.
		have "ang_eq D B C A B C" using equalanglesflip[OF `ang_eq C B D C B A`] .
		have "ang_eq A B C D B C" using equalanglessymmetric[OF `ang_eq D B C A B C`] .
		have "seg_eq A B D B \<and> seg_eq A C D C \<and> ang_eq B A C B D C" using Prop26A[OF `triangle A B C` `triangle D B C` `ang_eq A B C D B C` `ang_eq B C A B C D` `seg_eq B C B C`] .
		have "seg_eq A B D B" using `seg_eq A B D B \<and> seg_eq A C D C \<and> ang_eq B A C B D C` by blast
		have "seg_eq A C D C" using `seg_eq A B D B \<and> seg_eq A C D C \<and> ang_eq B A C B D C` by blast
		have "same_side A D B C" using `same_side A D B C` .
		have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
		have "A = D" using Prop07[OF `B \<noteq> C` `seg_eq A B D B` `seg_eq A C D C` `same_side A D B C`] .
		have "A \<noteq> D" using `A \<noteq> D` .
		show "False" using `A \<noteq> D` `A = D` by blast
	qed
	hence "parallel A D B C" by blast
	thus ?thesis by blast
qed

end