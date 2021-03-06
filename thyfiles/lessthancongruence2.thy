theory lessthancongruence2
	imports Geometry congruencetransitive
begin

theorem(in euclidean_geometry) lessthancongruence2:
	assumes 
		"seg_lt A B C D"
		"seg_eq A B E F"
	shows "seg_lt E F C D"
proof -
	obtain G where "bet C G D \<and> seg_eq C G A B" using lessthan_f[OF `seg_lt A B C D`]  by  blast
	have "bet C G D" using `bet C G D \<and> seg_eq C G A B` by blast
	have "seg_eq C G A B" using `bet C G D \<and> seg_eq C G A B` by blast
	have "seg_eq C G E F" using congruencetransitive[OF `seg_eq C G A B` `seg_eq A B E F`] .
	have "seg_lt E F C D" using lessthan_b[OF `bet C G D` `seg_eq C G E F`] .
	thus ?thesis by blast
qed

end