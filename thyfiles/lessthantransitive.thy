theory lessthantransitive
	imports n3_6a n3_6b Geometry betweennotequal congruencesymmetric congruencetransitive inequalitysymmetric layoff layoffunique ray1 ray4 sumofparts
begin

theorem(in euclidean_geometry) lessthantransitive:
	assumes 
		"seg_lt A B C D"
		"seg_lt C D E F"
	shows "seg_lt A B E F"
proof -
	obtain G where "bet C G D \<and> seg_eq C G A B" using lessthan_f[OF `seg_lt A B C D`]  by  blast
	have "bet C G D" using `bet C G D \<and> seg_eq C G A B` by blast
	have "seg_eq C G A B" using `bet C G D \<and> seg_eq C G A B` by blast
	obtain H where "bet E H F \<and> seg_eq E H C D" using lessthan_f[OF `seg_lt C D E F`]  by  blast
	have "bet E H F" using `bet E H F \<and> seg_eq E H C D` by blast
	have "seg_eq E H C D" using `bet E H F \<and> seg_eq E H C D` by blast
	have "E \<noteq> H" using betweennotequal[OF `bet E H F`] by blast
	have "C \<noteq> G" using betweennotequal[OF `bet C G D`] by blast
	obtain K where "ray_on E H K \<and> seg_eq E K C G" using layoff[OF `E \<noteq> H` `C \<noteq> G`]  by  blast
	have "ray_on E H K" using `ray_on E H K \<and> seg_eq E K C G` by blast
	have "seg_eq E K C G" using `ray_on E H K \<and> seg_eq E K C G` by blast
	have "seg_eq E K A B" using congruencetransitive[OF `seg_eq E K C G` `seg_eq C G A B`] .
	have "bet E K H \<or> H = K \<or> bet E H K" using ray1[OF `ray_on E H K`] .
	consider "bet E K H"|"H = K"|"bet E H K" using `bet E K H \<or> H = K \<or> bet E H K`  by blast
	hence "bet E K H"
	proof (cases)
		assume "bet E K H"
		thus ?thesis by blast
	next
		assume "H = K"
		have "seg_eq C G E K" using congruencesymmetric[OF `seg_eq E K C G`] .
		have "seg_eq C G E H" using `seg_eq C G E K` `H = K` by blast
		have "seg_eq E H C D" using `seg_eq E H C D` .
		have "seg_eq C G C D" using congruencetransitive[OF `seg_eq C G E H` `seg_eq E H C D`] .
		have "ray_on C G D" using ray4 `bet C G D \<and> seg_eq C G A B` `C \<noteq> G` by blast
		have "G = G" using equalityreflexiveE.
		have "ray_on C G G" using ray4 `G = G` `C \<noteq> G` by blast
		have "\<not> (\<not> (bet E K H))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E K H)))"
hence "\<not> (bet E K H)" by blast
			have "G = D" using layoffunique[OF `ray_on C G G` `ray_on C G D` `seg_eq C G C D`] .
			have "G \<noteq> D" using betweennotequal[OF `bet C G D`] by blast
			show "False" using `G \<noteq> D` `G = D` by blast
		qed
		hence "bet E K H" by blast
		thus ?thesis by blast
	next
		assume "bet E H K"
		have "seg_eq C D E H" using congruencesymmetric[OF `seg_eq E H C D`] .
		have "C \<noteq> D" using betweennotequal[OF `bet C G D`] by blast
		have "H \<noteq> K" using betweennotequal[OF `bet E H K`] by blast
		obtain J where "bet C D J \<and> seg_eq D J H K" using extensionE[OF `C \<noteq> D` `H \<noteq> K`]  by  blast
		have "bet C D J" using `bet C D J \<and> seg_eq D J H K` by blast
		have "ray_on C D J" using ray4 `bet C D J \<and> seg_eq D J H K` `C \<noteq> D` by blast
		have "ray_on C D G" using ray4 `bet C G D \<and> seg_eq C G A B` `C \<noteq> D` by blast
		have "seg_eq C D E H" using `seg_eq C D E H` .
		have "seg_eq D J H K" using `bet C D J \<and> seg_eq D J H K` by blast
		have "seg_eq C J E K" using sumofparts[OF `seg_eq C D E H` `seg_eq D J H K` `bet C D J` `bet E H K`] .
		have "seg_eq C J C G" using congruencetransitive[OF `seg_eq C J E K` `seg_eq E K C G`] .
		have "J = G" using layoffunique[OF `ray_on C D J` `ray_on C D G` `seg_eq C J C G`] .
		have "bet C D J" using `bet C D J` .
		have "bet C G D" using `bet C G D` .
		have "bet G D J" using n3_6a[OF `bet C G D` `bet C D J`] .
		have "\<not> (\<not> (bet E K H))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E K H)))"
hence "\<not> (bet E K H)" by blast
			have "G \<noteq> J" using betweennotequal[OF `bet G D J`] by blast
			have "J \<noteq> G" using inequalitysymmetric[OF `G \<noteq> J`] .
			show "False" using `J \<noteq> G` `J = G` by blast
		qed
		hence "bet E K H" by blast
		thus ?thesis by blast
	qed
	have "bet E H F" using `bet E H F` .
	have "bet E K F" using n3_6b[OF `bet E K H` `bet E H F`] .
	have "seg_lt A B E F" using lessthan_b[OF `bet E K F` `seg_eq E K A B`] .
	thus ?thesis by blast
qed

end