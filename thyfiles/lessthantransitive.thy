theory lessthantransitive
	imports Axioms Definitions Theorems
begin

theorem lessthantransitive:
	assumes: `axioms`
		"seg_lt A B C D"
		"seg_lt C D E F"
	shows: "seg_lt A B E F"
proof -
	obtain G where "bet C G D \<and> seg_eq C G A B" sorry
	have "bet C G D" using `bet C G D \<and> seg_eq C G A B` by blast
	have "seg_eq C G A B" using `bet C G D \<and> seg_eq C G A B` by blast
	obtain H where "bet E H F \<and> seg_eq E H C D" sorry
	have "bet E H F" using `bet E H F \<and> seg_eq E H C D` by blast
	have "seg_eq E H C D" using `bet E H F \<and> seg_eq E H C D` by blast
	have "E \<noteq> H" using betweennotequal[OF `axioms` `bet E H F`] by blast
	have "C \<noteq> G" using betweennotequal[OF `axioms` `bet C G D`] by blast
	obtain K where "ray_on E H K \<and> seg_eq E K C G" using layoff[OF `axioms` `E \<noteq> H` `C \<noteq> G`]  by  blast
	have "ray_on E H K" using `ray_on E H K \<and> seg_eq E K C G` by blast
	have "seg_eq E K C G" using `ray_on E H K \<and> seg_eq E K C G` by blast
	have "seg_eq E K A B" using congruencetransitive[OF `axioms` `seg_eq E K C G` `seg_eq C G A B`] .
	have "bet E K H \<or> H = K \<or> bet E H K" using ray1[OF `axioms` `ray_on E H K`] .
	consider "bet E K H"|"H = K"|"bet E H K" using `bet E K H \<or> H = K \<or> bet E H K`  by blast
	hence bet E K H
	proof (cases)
		case 1
	next
		case 2
		have "seg_eq C G E K" using congruencesymmetric[OF `axioms` `seg_eq E K C G`] .
		have "seg_eq C G E H" sorry
		have "seg_eq E H C D" using `seg_eq E H C D` .
		have "seg_eq C G C D" using congruencetransitive[OF `axioms` `seg_eq C G E H` `seg_eq E H C D`] .
		have "ray_on C G D" using ray4 `axioms` `bet C G D \<and> seg_eq C G A B` `C \<noteq> G` by blast
		have "G = G" using equalityreflexiveE[OF `axioms`] .
		have "ray_on C G G" using ray4 `axioms` `G = G` `C \<noteq> G` by blast
		have "bet E K H"
		proof (rule ccontr)
			assume "\<not> (bet E K H)"
			have "G = D" using layoffunique[OF `axioms` `ray_on C G G` `ray_on C G D` `seg_eq C G C D`] .
			have "G \<noteq> D" using betweennotequal[OF `axioms` `bet C G D`] by blast
			show "False" using `G \<noteq> D` `G = D` by blast
		qed
		hence "bet E K H" by blast
	next
		case 3
		have "seg_eq C D E H" using congruencesymmetric[OF `axioms` `seg_eq E H C D`] .
		have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C G D`] by blast
		have "H \<noteq> K" using betweennotequal[OF `axioms` `bet E H K`] by blast
		obtain J where "bet C D J \<and> seg_eq D J H K" using extensionE[OF `axioms` `C \<noteq> D` `H \<noteq> K`]  by  blast
		have "bet C D J" using `bet C D J \<and> seg_eq D J H K` by blast
		have "ray_on C D J" using ray4 `axioms` `bet C D J \<and> seg_eq D J H K` `C \<noteq> D` by blast
		have "ray_on C D G" using ray4 `axioms` `bet C G D \<and> seg_eq C G A B` `C \<noteq> D` by blast
		have "seg_eq C D E H" using `seg_eq C D E H` .
		have "seg_eq D J H K" using `bet C D J \<and> seg_eq D J H K` by blast
		have "seg_eq C J E K" using sumofparts[OF `axioms` `seg_eq C D E H` `seg_eq D J H K` `bet C D J` `bet E H K`] .
		have "seg_eq C J C G" using congruencetransitive[OF `axioms` `seg_eq C J E K` `seg_eq E K C G`] .
		have "J = G" using layoffunique[OF `axioms` `ray_on C D J` `ray_on C D G` `seg_eq C J C G`] .
		have "bet C D J" using `bet C D J` .
		have "bet C G D" using `bet C G D` .
		have "bet G D J" using n3_6a[OF `axioms` `bet C G D` `bet C D J`] .
		have "bet E K H"
		proof (rule ccontr)
			assume "\<not> (bet E K H)"
			have "G \<noteq> J" using betweennotequal[OF `axioms` `bet G D J`] by blast
			have "J \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> J`] .
			show "False" using `J \<noteq> G` `J = G` by blast
		qed
		hence "bet E K H" by blast
	next
	have "bet E H F" using `bet E H F` .
	have "bet E K F" using n3_6b[OF `axioms` `bet E K H` `bet E H F`] .
	have "seg_lt A B E F" sorry
	thus ?thesis by blast
qed

end