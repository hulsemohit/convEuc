theory congruencesymmetric
	imports Geometry
begin

theorem(in euclidean_geometry) congruencesymmetric:
	assumes 
		"seg_eq B C A D"
	shows "seg_eq A D B C"
proof -
	have "seg_eq B C B C" using congruencereflexiveE.
	have "seg_eq A D B C" using congruencetransitiveE[OF `seg_eq B C A D` `seg_eq B C B C`] .
	thus ?thesis by blast
qed

end