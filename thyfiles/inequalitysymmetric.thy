theory inequalitysymmetric
	imports Geometry equalitysymmetric
begin

theorem inequalitysymmetric:
	assumes "axioms"
		"A \<noteq> B"
	shows "B \<noteq> A"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		show "False" using `A = B` `A \<noteq> B` by blast
	qed
	hence "B \<noteq> A" by blast
	thus ?thesis by blast
qed

end