theory extensionunique
	imports Geometry congruencesymmetric
begin

theorem(in euclidean_geometry) extensionunique:
	assumes 
		"bet A B E"
		"bet A B F"
		"seg_eq B E B F"
	shows "E = F"
proof -
	have "seg_eq B E B E" using congruencereflexiveE.
	have "seg_eq B F B E" using congruencesymmetric[OF `seg_eq B E B F`] .
	have "seg_eq A E A E" using congruencereflexiveE.
	have "seg_eq A B A B" using congruencereflexiveE.
	have "seg_eq B E B F" using congruencesymmetric[OF `seg_eq B F B E`] .
	have "seg_eq E E E F" using n5_lineE[OF `seg_eq B E B F` `seg_eq A E A E` `seg_eq B E B E` `bet A B E` `bet A B F` `seg_eq A B A B`] .
	have "seg_eq E F E E" using congruencesymmetric[OF `seg_eq E E E F`] .
	have "E = F" using nullsegment1E[OF `seg_eq E F E E`] .
	thus ?thesis by blast
qed

end