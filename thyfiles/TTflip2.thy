theory TTflip2
	imports Geometry betweennotequal congruenceflip congruencesymmetric congruencetransitive inequalitysymmetric lessthancongruence2 nullsegment3 sumofparts
begin

theorem(in euclidean_geometry) TTflip2:
	assumes 
		"seg_sum_pair_gt A B C D E F G H"
	shows "seg_sum_pair_gt A B C D H G F E"
proof -
	obtain J where "bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J" using togetherfour_f[OF `seg_sum_pair_gt A B C D E F G H`]  by  blast
	have "bet E F J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_eq F J G H" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	have "seg_sum_gt A B C D E J" using `bet E F J \<and> seg_eq F J G H \<and> seg_sum_gt A B C D E J` by blast
	obtain K where "bet A B K \<and> seg_eq B K C D \<and> seg_lt E J A K" using togethergreater_f[OF `seg_sum_gt A B C D E J`]  by  blast
	have "bet A B K" using `bet A B K \<and> seg_eq B K C D \<and> seg_lt E J A K` by blast
	have "seg_eq B K C D" using `bet A B K \<and> seg_eq B K C D \<and> seg_lt E J A K` by blast
	have "seg_lt E J A K" using `bet A B K \<and> seg_eq B K C D \<and> seg_lt E J A K` by blast
	have "F \<noteq> J" using betweennotequal[OF `bet E F J`] by blast
	have "G \<noteq> H" using nullsegment3[OF `F \<noteq> J` `seg_eq F J G H`] .
	have "H \<noteq> G" using inequalitysymmetric[OF `G \<noteq> H`] .
	have "E \<noteq> F" using betweennotequal[OF `bet E F J`] by blast
	have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
	obtain L where "bet H G L \<and> seg_eq G L F E" using extensionE[OF `H \<noteq> G` `F \<noteq> E`]  by  blast
	have "bet H G L" using `bet H G L \<and> seg_eq G L F E` by blast
	have "seg_eq G L F E" using `bet H G L \<and> seg_eq G L F E` by blast
	have "seg_eq L G E F" using congruenceflip[OF `seg_eq G L F E`] by blast
	have "seg_eq G H F J" using congruencesymmetric[OF `seg_eq F J G H`] .
	have "bet L G H" using betweennesssymmetryE[OF `bet H G L`] .
	have "seg_eq L H E J" using sumofparts[OF `seg_eq L G E F` `seg_eq G H F J` `bet L G H` `bet E F J`] .
	have "seg_eq H L L H" using equalityreverseE.
	have "seg_eq H L E J" using congruencetransitive[OF `seg_eq H L L H` `seg_eq L H E J`] .
	have "seg_eq E J H L" using congruencesymmetric[OF `seg_eq H L E J`] .
	have "seg_lt H L A K" using lessthancongruence2[OF `seg_lt E J A K` `seg_eq E J H L`] .
	have "bet A B K \<and> seg_eq B K C D \<and> seg_lt H L A K" using `bet A B K \<and> seg_eq B K C D \<and> seg_lt E J A K` `bet A B K \<and> seg_eq B K C D \<and> seg_lt E J A K` `seg_lt H L A K` by blast
	have "seg_sum_gt A B C D H L" using togethergreater_b[OF `bet A B K` `seg_eq B K C D` `seg_lt H L A K`] .
	have "bet H G L \<and> seg_eq G L F E \<and> seg_sum_gt A B C D H L" using `bet H G L \<and> seg_eq G L F E` `bet H G L \<and> seg_eq G L F E` `seg_sum_gt A B C D H L` by blast
	have "seg_sum_pair_gt A B C D H G F E" using togetherfour_b[OF `bet H G L` `seg_eq G L F E` `seg_sum_gt A B C D H L`] .
	thus ?thesis by blast
qed

end