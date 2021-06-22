theory supplementsymmetric
	imports Axioms Definitions Theorems
begin

theorem supplementsymmetric:
	assumes: `axioms`
		"linear_pair A B C E D"
	shows: "linear_pair D B E C A"
proof -
	have "ray_on B C E \<and> bet A B D" using supplement_f[OF `axioms` `linear_pair A B C E D`] .
	have "ray_on B C E" using `ray_on B C E \<and> bet A B D` by blast
	have "bet A B D" using `ray_on B C E \<and> bet A B D` by blast
	have "bet D B A" using betweennesssymmetryE[OF `axioms` `bet A B D`] .
	have "ray_on B E C" using ray5[OF `axioms` `ray_on B C E`] .
	have "linear_pair D B E C A" using supplement_b[OF `axioms` `ray_on B E C` `bet D B A`] .
	thus ?thesis by blast
qed

end