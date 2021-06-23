theory n3_6a
	imports Geometry
begin

theorem n3_6a:
	assumes "axioms"
		"bet A B C"
		"bet A C D"
	shows "bet B C D"
proof -
	have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
	have "bet D C A" using betweennesssymmetryE[OF `axioms` `bet A C D`] .
	have "bet D C B" using innertransitivityE[OF `axioms` `bet D C A` `bet C B A`] .
	have "bet B C D" using betweennesssymmetryE[OF `axioms` `bet D C B`] .
	thus ?thesis by blast
qed

end