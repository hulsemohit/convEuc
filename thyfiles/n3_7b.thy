theory n3_7b
	imports n3_7a Geometry
begin

theorem n3_7b:
	assumes "axioms"
		"bet A B C"
		"bet B C D"
	shows "bet A B D"
proof -
	have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
	have "bet D C B" using betweennesssymmetryE[OF `axioms` `bet B C D`] .
	have "bet D B A" using n3_7a[OF `axioms` `bet D C B` `bet C B A`] .
	have "bet A B D" using betweennesssymmetryE[OF `axioms` `bet D B A`] .
	thus ?thesis by blast
qed

end