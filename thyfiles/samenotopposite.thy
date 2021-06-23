theory samenotopposite
	imports Geometry planeseparation samesidesymmetric
begin

theorem samenotopposite:
	assumes "axioms"
		"same_side A B C D"
	shows "\<not> (oppo_side A C D B)"
proof -
	have "same_side B A C D" using samesidesymmetric[OF `axioms` `same_side A B C D`] by blast
	have "\<not> (oppo_side A C D B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (oppo_side A C D B))"
hence "oppo_side A C D B" by blast
		have "oppo_side B C D B" using planeseparation[OF `axioms` `same_side B A C D` `oppo_side A C D B`] .
		obtain M where "bet B M B" using oppositeside_f[OF `axioms` `oppo_side B C D B`] by blast
		have "\<not> (bet B M B)" using betweennessidentityE[OF `axioms`] .
		show "False" using `\<not> (bet B M B)` `bet B M B` by blast
	qed
	hence "\<not> (oppo_side A C D B)" by blast
	thus ?thesis by blast
qed

end