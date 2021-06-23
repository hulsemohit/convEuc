theory supplementsymmetric
	imports Geometry ray5
begin

theorem supplementsymmetric:
	assumes "axioms"
		"supplement A B C E D"
	shows "supplement D B E C A"
proof -
	have "ray_on B C E \<and> bet A B D" using supplement_f[OF `axioms` `supplement A B C E D`] .
	have "ray_on B C E" using `ray_on B C E \<and> bet A B D` by blast
	have "bet A B D" using `ray_on B C E \<and> bet A B D` by blast
	have "bet D B A" using betweennesssymmetryE[OF `axioms` `bet A B D`] .
	have "ray_on B E C" using ray5[OF `axioms` `ray_on B C E`] .
	have "supplement D B E C A" using supplement_b[OF `axioms` `ray_on B E C` `bet D B A`] .
	thus ?thesis by blast
qed

end