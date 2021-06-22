theory Prop33B
	imports Axioms Definitions Theorems
begin

theorem Prop33B:
	assumes: `axioms`
		"parallel A B C D"
		"seg_eq A B C D"
		"same_side A C B D"
	shows: "parallel A C B D \<and> seg_eq A C B D"
proof -
	have "\<not> (cross A C B D)"
	proof (rule ccontr)
		assume "cross A C B D"
		obtain M where "bet A M C \<and> bet B M D" using cross_f[OF `axioms` `cross A C B D`] by blast
		have "bet A M C" using `bet A M C \<and> bet B M D` by blast
		have "bet B M D" using `bet A M C \<and> bet B M D` by blast
		have "col B M D" using collinear_b `axioms` `bet A M C \<and> bet B M D` by blast
		have "col B D M" using collinearorder[OF `axioms` `col B M D`] by blast
		have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A B C D`] by blast
		have "\<not> col B D A" using NCorder[OF `axioms` `\<not> col A B D`] by blast
		have "bet A M C \<and> col B D M \<and> \<not> col B D A" using `bet A M C \<and> bet B M D` `col B D M` `\<not> col B D A` by blast
		have "oppo_side A B D C" using oppositeside_b[OF `axioms` `bet A M C` `col B D M` `\<not> col B D A`] .
		have "\<not> (oppo_side A B D C)" using samenotopposite[OF `axioms` `same_side A C B D`] .
		show "False" using `\<not> (oppo_side A B D C)` `oppo_side A B D C` by blast
	qed
	hence "\<not> (cross A C B D)" by blast
	have "cross A D C B" using crisscross[OF `axioms` `parallel A B C D` `\<not> (cross A C B D)`] .
	obtain m where "bet A m D \<and> bet C m B" using cross_f[OF `axioms` `cross A D C B`] by blast
	have "bet A m D" using `bet A m D \<and> bet C m B` by blast
	have "bet C m B" using `bet A m D \<and> bet C m B` by blast
	have "bet B m C" using betweennesssymmetryE[OF `axioms` `bet C m B`] .
	have "parallel A C B D \<and> seg_eq A C B D" using Prop33[OF `axioms` `parallel A B C D` `seg_eq A B C D` `bet A m D` `bet B m C`] .
	thus ?thesis by blast
qed

end