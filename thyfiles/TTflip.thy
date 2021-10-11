theory TTflip
	imports Geometry TGflip TGsymmetric
begin

theorem(in euclidean_geometry) TTflip:
	assumes 
		"seg_sum_pair_gt A B C D E F G H"
	shows "seg_sum_pair_gt B A D C E F G H"
proof -
	obtain J where "bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J" using togetherfour_f[OF `seg_sum_pair_gt A B C D E F G H`]  by  blast
	have "bet E F J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_eq F J G H" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt A B C D E J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt B A C D E J" using TGflip[OF `seg_sum_gt A B C D E J`] by blast
	have "seg_sum_gt C D B A E J" using TGsymmetric[OF `seg_sum_gt B A C D E J`] .
	have "seg_sum_gt D C B A E J" using TGflip[OF `seg_sum_gt C D B A E J`] by blast
	have "seg_sum_gt B A D C E J" using TGsymmetric[OF `seg_sum_gt D C B A E J`] .
	have "seg_sum_pair_gt B A D C E F G H" using togetherfour_b[OF `bet E F J` `seg_eq F J G H` `seg_sum_gt B A D C E J`] .
	thus ?thesis by blast
qed

end