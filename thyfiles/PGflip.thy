theory PGflip
	imports Axioms Definitions Theorems
begin

theorem PGflip:
	assumes: `axioms`
		"parallelogram A B C D"
	shows: "parallelogram B A D C"
proof -
	have "parallel A B C D \<and> parallel A D B C" sorry
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel B A D C" using parallelflip[OF `axioms` `parallel A B C D`] by blast
	have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
	have "parallel B A D C \<and> parallel B C A D" using `parallel B A D C` `parallel B C A D` by blast
	have "parallelogram B A D C" sorry
	thus ?thesis by blast
qed

end