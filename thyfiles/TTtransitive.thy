theory TTtransitive
	imports Axioms Definitions Theorems
begin

theorem TTtransitive:
	assumes: `axioms`
		"seg_sum_pair_gt A B C D E F G H"
		"seg_sum_pair_gt E F G H P Q R S"
	shows: "seg_sum_pair_gt A B C D P Q R S"
proof -
	obtain K where "bet E F K \<and> seg_eq F K G H \<and> seg_sum_gt A B C D E K" sorry
	have "bet E F K" using `bet E F K \<and> seg_eq F K G H \<and> seg_sum_gt A B C D E K` by blast
	have "seg_sum_gt A B C D E K" using `bet E F K \<and> seg_eq F K G H \<and> seg_sum_gt A B C D E K` by blast
	obtain J where "bet A B J \<and> seg_eq B J C D \<and> seg_lt E K A J" sorry
	have "bet A B J" using `bet A B J \<and> seg_eq B J C D \<and> seg_lt E K A J` by blast
	have "seg_eq B J C D" using `bet A B J \<and> seg_eq B J C D \<and> seg_lt E K A J` by blast
	have "seg_lt E K A J" using `bet A B J \<and> seg_eq B J C D \<and> seg_lt E K A J` by blast
	obtain L where "bet P Q L \<and> seg_eq Q L R S \<and> seg_sum_gt E F G H P L" sorry
	have "bet P Q L" using `bet P Q L \<and> seg_eq Q L R S \<and> seg_sum_gt E F G H P L` by blast
	have "seg_eq Q L R S" using `bet P Q L \<and> seg_eq Q L R S \<and> seg_sum_gt E F G H P L` by blast
	have "seg_sum_gt E F G H P L" using `bet P Q L \<and> seg_eq Q L R S \<and> seg_sum_gt E F G H P L` by blast
	obtain M where "bet E F M \<and> seg_eq F M G H \<and> seg_lt P L E M" sorry
	have "bet E F M" using `bet E F M \<and> seg_eq F M G H \<and> seg_lt P L E M` by blast
	have "seg_lt P L E M" using `bet E F M \<and> seg_eq F M G H \<and> seg_lt P L E M` by blast
	have "K = K" using equalityreflexiveE[OF `axioms`] .
	have "F \<noteq> K" using betweennotequal[OF `axioms` `bet E F K`] by blast
	have "ray_on F K M" sorry
	have "ray_on F K K" using ray4 `axioms` `K = K` `F \<noteq> K` by blast
	have "seg_eq F K G H" using `bet E F K \<and> seg_eq F K G H \<and> seg_sum_gt A B C D E K` by blast
	have "seg_eq F M G H" using `bet E F M \<and> seg_eq F M G H \<and> seg_lt P L E M` by blast
	have "seg_eq G H F M" using congruencesymmetric[OF `axioms` `seg_eq F M G H`] .
	have "seg_eq F K F M" using congruencetransitive[OF `axioms` `seg_eq F K G H` `seg_eq G H F M`] .
	have "K = M" using layoffunique[OF `axioms` `ray_on F K K` `ray_on F K M` `seg_eq F K F M`] .
	have "seg_lt P L E K" sorry
	have "seg_lt P L A J" using lessthantransitive[OF `axioms` `seg_lt P L E K` `seg_lt E K A J`] .
	have "seg_sum_gt A B C D P L" sorry
	have "seg_sum_pair_gt A B C D P Q R S" sorry
	thus ?thesis by blast
qed

end