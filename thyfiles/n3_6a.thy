theory n3_6a
	imports Geometry
begin

theorem(in euclidean_geometry) n3_6a:
	assumes 
		"bet A B C"
		"bet A C D"
	shows "bet B C D"
proof -
	have "bet C B A" using betweennesssymmetryE[OF `bet A B C`] .
	have "bet D C A" using betweennesssymmetryE[OF `bet A C D`] .
	have "bet D C B" using innertransitivityE[OF `bet D C A` `bet C B A`] .
	have "bet B C D" using betweennesssymmetryE[OF `bet D C B`] .
	thus ?thesis by blast
qed

end