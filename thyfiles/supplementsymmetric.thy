theory supplementsymmetric
	imports Geometry ray5
begin

theorem(in euclidean_geometry) supplementsymmetric:
	assumes 
		"supplement A B C E D"
	shows "supplement D B E C A"
proof -
	have "ray_on B C E \<and> bet A B D" using supplement_f[OF `supplement A B C E D`] .
	have "ray_on B C E" using `ray_on B C E \<and> bet A B D` by blast
	have "bet A B D" using `ray_on B C E \<and> bet A B D` by blast
	have "bet D B A" using betweennesssymmetryE[OF `bet A B D`] .
	have "ray_on B E C" using ray5[OF `ray_on B C E`] .
	have "supplement D B E C A" using supplement_b[OF `ray_on B E C` `bet D B A`] .
	thus ?thesis by blast
qed

end