theory TTflip
	imports Axioms Definitions Theorems
begin

theorem TTflip:
	assumes: `axioms`
		"seg_sum_pair_gt A B C D E F G H"
	shows: "seg_sum_pair_gt B A D C E F G H"
proof -
	obtain J where "bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J" sorry
	have "bet E F J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_eq F J G H" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt A B C D E J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt B A C D E J" using TGflip[OF `axioms` `seg_sum_gt A B C D E J`] by blast
	have "seg_sum_gt C D B A E J" using TGsymmetric[OF `axioms` `seg_sum_gt B A C D E J`] .
	have "seg_sum_gt D C B A E J" using TGflip[OF `axioms` `seg_sum_gt C D B A E J`] by blast
	have "seg_sum_gt B A D C E J" using TGsymmetric[OF `axioms` `seg_sum_gt D C B A E J`] .
	have "seg_sum_pair_gt B A D C E F G H" sorry
	thus ?thesis by blast
qed

end