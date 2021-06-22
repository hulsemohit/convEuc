theory TCreflexive
	imports Axioms Definitions Theorems
begin

theorem TCreflexive:
	assumes: `axioms`
		"triangle A B C"
	shows: "tri_cong A B C A B C"
proof -
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] .
	have "tri_cong A B C A B C" sorry
	thus ?thesis by blast
qed

end