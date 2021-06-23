theory PGrotate
	imports Geometry parallelflip parallelsymmetric
begin

theorem PGrotate:
	assumes "axioms"
		"parallelogram A B C D"
	shows "parallelogram B C D A"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `axioms` `parallelogram A B C D`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
	have "parallel B C D A" using parallelflip[OF `axioms` `parallel B C A D`] by blast
	have "parallel B A C D" using parallelflip[OF `axioms` `parallel A B C D`] by blast
	have "parallel B C D A \<and> parallel B A C D" using `parallel B C D A` `parallel B A C D` by blast
	have "parallelogram B C D A" using parallelogram_b[OF `axioms` `parallel B C D A` `parallel B A C D`] .
	thus ?thesis by blast
qed

end