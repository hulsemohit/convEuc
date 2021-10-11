theory n4_19
	imports Geometry congruencesymmetric equalitysymmetric interior5
begin

theorem(in euclidean_geometry) n4_19:
	assumes 
		"bet A D B"
		"seg_eq A C A D"
		"seg_eq B D B C"
	shows "C = D"
proof -
	have "seg_eq A D A D" using congruencereflexiveE.
	have "seg_eq D B D B" using congruencereflexiveE.
	have "seg_eq B C B D" using congruencesymmetric[OF `seg_eq B D B C`] .
	have "seg_eq A C A D" using `seg_eq A C A D` .
	have "seg_eq D C D D" using interior5[OF `bet A D B` `bet A D B` `seg_eq A D A D` `seg_eq D B D B` `seg_eq A C A D` `seg_eq B C B D`] .
	have "D = C" using nullsegment1E[OF `seg_eq D C D D`] .
	have "C = D" using equalitysymmetric[OF `D = C`] .
	thus ?thesis by blast
qed

end