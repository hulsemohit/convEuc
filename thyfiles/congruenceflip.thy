theory congruenceflip
	imports Geometry congruencetransitive
begin

theorem congruenceflip:
	assumes "axioms"
		"seg_eq A B C D"
	shows "seg_eq B A D C \<and> seg_eq B A C D \<and> seg_eq A B D C"
proof -
	have "seg_eq B A A B" using equalityreverseE[OF `axioms`] .
	have "seg_eq C D D C" using equalityreverseE[OF `axioms`] .
	have "seg_eq B A C D" using congruencetransitive[OF `axioms` `seg_eq B A A B` `seg_eq A B C D`] .
	have "seg_eq A B D C" using congruencetransitive[OF `axioms` `seg_eq A B C D` `seg_eq C D D C`] .
	have "seg_eq B A D C" using congruencetransitive[OF `axioms` `seg_eq B A A B` `seg_eq A B D C`] .
	have "seg_eq B A D C \<and> seg_eq B A C D \<and> seg_eq A B D C" using `seg_eq B A D C` `seg_eq B A C D` `seg_eq A B D C` by blast
	thus ?thesis by blast
qed

end