theory TTorder
	imports Axioms Definitions Theorems
begin

theorem TTorder:
	assumes: `axioms`
		"seg_sum_pair_gt A B C D E F G H"
	shows: "seg_sum_pair_gt C D A B E F G H"
proof -
	obtain J where "bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J" sorry
	have "bet E F J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_eq F J G H" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt A B C D E J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt C D A B E J" using TGsymmetric[OF `axioms` `seg_sum_gt A B C D E J`] .
	have "seg_sum_pair_gt C D A B E F G H" sorry
	thus ?thesis by blast
qed

end