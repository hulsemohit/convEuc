theory equalitysymmetric
	imports Geometry
begin

theorem(in euclidean_geometry) equalitysymmetric:
	assumes 
		"B = A"
	shows "A = B"
proof -
	have "A = A" using equalityreflexiveE.
	have "A = B" using equalitytransitiveE[OF `A = A` `B = A`] .
	thus ?thesis by blast
qed

end