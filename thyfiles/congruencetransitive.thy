theory congruencetransitive
	imports Geometry congruencesymmetric
begin

theorem(in euclidean_geometry) congruencetransitive:
	assumes 
		"seg_eq A B C D"
		"seg_eq C D E F"
	shows "seg_eq A B E F"
proof -
	have "seg_eq C D A B" using congruencesymmetric[OF `seg_eq A B C D`] .
	have "seg_eq A B E F" using congruencetransitiveE[OF `seg_eq C D A B` `seg_eq C D E F`] .
	thus ?thesis by blast
qed

end