theory TCreflexive
	imports Geometry
begin

theorem TCreflexive:
	assumes "axioms"
		"triangle A B C"
	shows "tri_cong A B C A B C"
proof -
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] .
	have "tri_cong A B C A B C" using trianglecongruence_b[OF `axioms` `seg_eq A B A B` `seg_eq B C B C` `seg_eq A C A C` `triangle A B C`] .
	thus ?thesis by blast
qed

end