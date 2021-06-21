theory doublereverse
	imports Axioms Definitions Theorems
begin

theorem doublereverse:
	assumes: `axioms`
		"seg_eq A B C D"
	shows: "seg_eq D C B A \<and> seg_eq B A D C"
proof -
	have "seg_eq C D D C" sorry
	have "seg_eq A B D C" using congruencetransitive[OF `axioms` `seg_eq A B C D` `seg_eq C D D C`] .
	have "seg_eq B A A B" sorry
	have "seg_eq B A D C" using congruencetransitive[OF `axioms` `seg_eq B A A B` `seg_eq A B D C`] .
	have "seg_eq D C B A" using congruencesymmetric[OF `axioms` `seg_eq B A D C`] .
	have "seg_eq D C B A \<and> seg_eq B A D C"  using `seg_eq D C B A` `seg_eq B A D C` by simp
	thus ?thesis by blast
qed