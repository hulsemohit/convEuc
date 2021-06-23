theory equalitysymmetric
	imports Geometry
begin

theorem equalitysymmetric:
	assumes "axioms"
		"B = A"
	shows "A = B"
proof -
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "A = B" using equalitytransitiveE[OF `axioms` `A = A` `B = A`] .
	thus ?thesis by blast
qed

end