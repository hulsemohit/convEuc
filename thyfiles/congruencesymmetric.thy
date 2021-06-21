theory congruencesymmetric
	imports Axioms Definitions Theorems
begin

theorem congruencesymmetric:
	assumes: `axioms`
		"seg_eq B C A D"
	shows: "seg_eq A D B C"
proof -
	have "seg_eq B C B C" sorry
	have "seg_eq A D B C" sorry
	thus ?thesis by blast
qed