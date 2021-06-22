theory inequalitysymmetric
	imports Axioms Definitions Theorems
begin

theorem inequalitysymmetric:
	assumes: `axioms`
		"A \<noteq> B"
	shows: "B \<noteq> A"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "B = A"
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		show "False" using `A = B` `A \<noteq> B` by blast
	qed
	hence "B \<noteq> A" by blast
	thus ?thesis by blast
qed

end