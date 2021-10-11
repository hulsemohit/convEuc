theory Prop33B
	imports Geometry NCorder Prop33 collinearorder crisscross parallelNC samenotopposite
begin

theorem(in euclidean_geometry) Prop33B:
	assumes 
		"parallel A B C D"
		"seg_eq A B C D"
		"same_side A C B D"
	shows "parallel A C B D \<and> seg_eq A C B D"
proof -
	have "\<not> (cross A C B D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (cross A C B D))"
hence "cross A C B D" by blast
		obtain M where "bet A M C \<and> bet B M D" using cross_f[OF `cross A C B D`]  by  blast
		have "bet A M C" using `bet A M C \<and> bet B M D` by blast
		have "bet B M D" using `bet A M C \<and> bet B M D` by blast
		have "col B M D" using collinear_b `bet A M C \<and> bet B M D` by blast
		have "col B D M" using collinearorder[OF `col B M D`] by blast
		have "\<not> col A B D" using parallelNC[OF `parallel A B C D`] by blast
		have "\<not> col B D A" using NCorder[OF `\<not> col A B D`] by blast
		have "bet A M C \<and> col B D M \<and> \<not> col B D A" using `bet A M C \<and> bet B M D` `col B D M` `\<not> col B D A` by blast
		have "oppo_side A B D C" using oppositeside_b[OF `bet A M C` `col B D M` `\<not> col B D A`] .
		have "\<not> (oppo_side A B D C)" using samenotopposite[OF `same_side A C B D`] .
		show "False" using `\<not> (oppo_side A B D C)` `oppo_side A B D C` by blast
	qed
	hence "\<not> (cross A C B D)" by blast
	have "cross A D C B" using crisscross[OF `parallel A B C D` `\<not> (cross A C B D)`] .
	obtain m where "bet A m D \<and> bet C m B" using cross_f[OF `cross A D C B`]  by  blast
	have "bet A m D" using `bet A m D \<and> bet C m B` by blast
	have "bet C m B" using `bet A m D \<and> bet C m B` by blast
	have "bet B m C" using betweennesssymmetryE[OF `bet C m B`] .
	have "parallel A C B D \<and> seg_eq A C B D" using Prop33[OF `parallel A B C D` `seg_eq A B C D` `bet A m D` `bet B m C`] .
	thus ?thesis by blast
qed

end