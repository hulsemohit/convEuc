theory congruencesymmetric
	imports Geometry
begin

theorem congruencesymmetric:
	assumes "axioms"
		"seg_eq B C A D"
	shows "seg_eq A D B C"
proof -
	have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A D B C" using congruencetransitiveE[OF `axioms` `seg_eq B C A D` `seg_eq B C B C`] .
	thus ?thesis by blast
qed

end