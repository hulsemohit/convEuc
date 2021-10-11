theory n3_6b
	imports n3_5b Geometry
begin

theorem(in euclidean_geometry) n3_6b:
	assumes 
		"bet A B C"
		"bet A C D"
	shows "bet A B D"
proof -
	have "bet C B A" using betweennesssymmetryE[OF `bet A B C`] .
	have "bet D C A" using betweennesssymmetryE[OF `bet A C D`] .
	have "bet D B A" using n3_5b[OF `bet D C A` `bet C B A`] .
	have "bet A B D" using betweennesssymmetryE[OF `bet D B A`] .
	thus ?thesis by blast
qed

end