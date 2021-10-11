theory n3_7b
	imports n3_7a Geometry
begin

theorem(in euclidean_geometry) n3_7b:
	assumes 
		"bet A B C"
		"bet B C D"
	shows "bet A B D"
proof -
	have "bet C B A" using betweennesssymmetryE[OF `bet A B C`] .
	have "bet D C B" using betweennesssymmetryE[OF `bet B C D`] .
	have "bet D B A" using n3_7a[OF `bet D C B` `bet C B A`] .
	have "bet A B D" using betweennesssymmetryE[OF `bet D B A`] .
	thus ?thesis by blast
qed

end