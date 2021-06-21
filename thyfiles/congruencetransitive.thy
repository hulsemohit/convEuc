theory congruencetransitive
	imports Axioms Definitions Theorems
begin

theorem congruencetransitive:
	assumes: `axioms`
		"seg_eq A B C D"
		"seg_eq C D E F"
	shows: "seg_eq A B E F"
proof -
	have "seg_eq C D A B" using congruencesymmetric[OF `axioms` `seg_eq A B C D`] .
	have "seg_eq A B E F" sorry
	thus ?thesis by blast
qed