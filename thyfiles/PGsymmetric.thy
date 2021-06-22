theory PGsymmetric
	imports Axioms Definitions Theorems
begin

theorem PGsymmetric:
	assumes: `axioms`
		"parallelogram A B C D"
	shows: "parallelogram C D A B"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `axioms` `parallelogram A B C D`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel C D A B" using parallelsymmetric[OF `axioms` `parallel A B C D`] .
	have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
	have "parallel C B D A" using parallelflip[OF `axioms` `parallel B C A D`] by blast
	have "parallel C D A B \<and> parallel C B D A" using `parallel C D A B` `parallel C B D A` by blast
	have "parallelogram C D A B" using parallelogram_b[OF `axioms` `parallel C D A B` `parallel C B D A`] .
	thus ?thesis by blast
qed

end