theory TCreflexive
	imports Geometry
begin

theorem(in euclidean_geometry) TCreflexive:
	assumes 
		"triangle A B C"
	shows "tri_cong A B C A B C"
proof -
	have "seg_eq A B A B" using congruencereflexiveE.
	have "seg_eq B C B C" using congruencereflexiveE.
	have "seg_eq A C A C" using congruencereflexiveE.
	have "tri_cong A B C A B C" using trianglecongruence_b[OF `seg_eq A B A B` `seg_eq B C B C` `seg_eq A C A C` `triangle A B C`] .
	thus ?thesis by blast
qed

end