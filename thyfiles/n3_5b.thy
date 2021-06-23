theory n3_5b
	imports n3_7a Geometry
begin

theorem n3_5b:
	assumes "axioms"
		"bet A B D"
		"bet B C D"
	shows "bet A C D"
proof -
	have "bet A B C" using innertransitivityE[OF `axioms` `bet A B D` `bet B C D`] .
	have "bet A C D" using n3_7a[OF `axioms` `bet A B C` `bet B C D`] .
	thus ?thesis by blast
qed

end